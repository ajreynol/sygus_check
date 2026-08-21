#!/usr/bin/env python3
"""Regression tests for sygus-check.

Each case names a solution file, a problem file and the expected verdict.
Cases whose expectation is only about the syntactic check run with
--no-semantic so the suite does not need a solver for them.
"""

import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CASES = os.path.join(HERE, "cases")
TOOL = os.path.join(ROOT, "sygus-check")

# (solution, problem, extra args, expected verdict)
TESTS = [
    ("max2-correct.out",       "max2.sy", [], "correct"),
    ("max2-let.out",           "max2.sy", [], "correct"),
    ("max2-renamed.out",       "max2.sy", [], "correct"),
    ("max2-semantic-bad.out",  "max2.sy", [], "incorrect"),
    ("max2-syntactic-bad.out", "max2.sy", ["--no-semantic"], "incorrect"),
    ("max2-syntactic-bad.out", "max2.sy", ["--no-syntactic"], "correct"),
    ("max2-badsig.out",        "max2.sy", ["--no-semantic"], "incorrect"),
    ("inv-correct.out",        "inv.sy",  [], "correct"),
    ("inv-bad.out",            "inv.sy",  [], "incorrect"),
    ("bv-correct.out",         "bv.sy",   [], "correct"),
    ("bv-const.out",           "bv.sy",   [], "correct"),
    ("bv-syntactic-bad.out",   "bv.sy",   ["--no-semantic"], "incorrect"),
    ("lin-correct.out",        "lin.sy",  [], "correct"),
    ("lin-bad.out",            "lin.sy",  [], "incorrect"),
    ("strings-correct.out",    "strings.sy", [], "correct"),
    ("grammar-find.out",       "grammar-find.sy", [], "correct"),
    # Operator arity is part of the grammar: (+ T T) does not generate a
    # variadic application such as (+ 1 1 1).
    ("arity-correct.out",        "arity.sy", [], "correct"),
    ("arity-nested-correct.out", "arity.sy", [], "correct"),
    ("arity-plus3.out",          "arity.sy", ["--no-semantic"], "incorrect"),
    ("arity-plus1.out",          "arity.sy", ["--no-semantic"], "incorrect"),
    ("arity-minus2.out",         "arity.sy", ["--no-semantic"], "incorrect"),
    ("arity-nested-bad.out",     "arity.sy", ["--no-semantic"], "incorrect"),
]

EXPECTED_EXIT = {"correct": 0, "incorrect": 1, "unknown": 2}


def run_case(sol, prob, extra, expect, solver):
    cmd = [sys.executable, TOOL, "--no-color", "--solver", solver,
           os.path.join(CASES, sol), os.path.join(CASES, prob)] + extra
    p = subprocess.run(cmd, capture_output=True, text=True)
    got = p.returncode
    want = EXPECTED_EXIT[expect]
    label = "%s + %s %s" % (sol, prob, " ".join(extra))
    if got == want:
        print("PASS  %s" % label)
        return True
    print("FAIL  %s: expected %s (exit %d), got exit %d" % (label, expect, want, got))
    print(p.stdout + p.stderr)
    return False


def unit_tests():
    sys.path.insert(0, ROOT)
    from sygus_check.problem import Problem
    from sygus_check.sexpr import parse, to_str
    from sygus_check.solution import Solution
    from sygus_check.terms import expand_lets, literal_sorts

    ok = True

    def eq(what, got, want):
        nonlocal ok
        if got != want:
            print("FAIL  unit %s: got %r, want %r" % (what, got, want))
            ok = False
        else:
            print("PASS  unit %s" % what)

    eq("comments", to_str(parse("(a ; comment\n b)")[0]), "(a b)")
    eq("strings", to_str(parse('(a "b ; c" |d e|)')[0]), '(a "b ; c" |d e|)')
    eq("let expansion", to_str(expand_lets(parse("(let ((x 1)) (+ x x))")[0])),
       "(+ 1 1)")
    eq("nested let", to_str(expand_lets(parse("(let ((x 1)) (let ((y x)) (+ x y)))")[0])),
       "(+ 1 1)")
    eq("capture avoidance",
       to_str(expand_lets(parse("(let ((x y)) (forall ((y Int)) (= x y)))")[0])),
       "(forall ((y!1 Int)) (= y y!1))")
    eq("literal Int", literal_sorts("3"), ["Int", "Real"])
    eq("literal BV hex", literal_sorts("#x0f"), ["(_ BitVec 8)"])
    eq("literal neg", literal_sorts(parse("(- 3)")[0]), ["Int", "Real"])
    eq("literal rational", literal_sorts(parse("(/ 1 2)")[0]), ["Real"])
    eq("not a literal", literal_sorts(parse("(+ 1 x)")[0]), None)

    p = Problem.from_string(
        "(set-logic LIA)(define-sort I () Int)"
        "(synth-fun f ((x I)) I ((S I)) ((S I (x (Constant I)))))"
        "(declare-var y Int)(constraint (= (f y) y))(check-synth)")
    eq("sort alias", p.sorts.canon(parse("I")[0]), "Int")
    eq("synth arity", len(p.synth["f"].args), 1)
    eq("grammar start", p.synth["f"].grammar.start, "S")

    s = Solution.from_string("sat\n(\n(define-fun f ((x Int)) Int x)\n)")
    eq("solution status", s.status, "sat")
    eq("solution defs", [d.name for d in s.defs], ["f"])
    s = Solution.from_string("(define-fun f ((x Int)) Int x)")
    eq("unwrapped solution", [d.name for d in s.defs], ["f"])
    return ok


def option_tests(solver):
    """The verification condition must be inspectable from the command line."""
    import tempfile

    ok = True

    def eq(what, got, want):
        nonlocal ok
        if got != want:
            print("FAIL  option %s: got %r, want %r" % (what, got, want))
            ok = False
        else:
            print("PASS  option %s" % what)

    sol = os.path.join(CASES, "max2-correct.out")
    prob = os.path.join(CASES, "max2.sy")
    base = [sys.executable, TOOL, "--no-color", "--solver", solver, sol, prob]

    p = subprocess.run(base + ["--print-vc"], capture_output=True, text=True)
    eq("--print-vc emits a check-sat", "(check-sat)" in p.stdout, True)
    eq("--print-vc runs no check", "result:" in p.stdout, False)

    with tempfile.TemporaryDirectory() as d:
        out = os.path.join(d, "vc.smt2")
        p = subprocess.run(base + ["--vc-out", out], capture_output=True, text=True)
        eq("--vc-out exit code", p.returncode, 0)
        eq("--vc-out still checks", "result: correct" in p.stdout, True)
        eq("--vc-out wrote the file", os.path.exists(out), True)
        eq("--vc-out content", "(check-sat)" in open(out).read(), True)

        out2 = os.path.join(d, "nosem.smt2")
        p = subprocess.run(base + ["--no-semantic", "--vc-out", out2],
                           capture_output=True, text=True)
        eq("--vc-out with --no-semantic", os.path.exists(out2), True)

        p = subprocess.run(base + ["--keep-vc", "--workdir", d],
                           capture_output=True, text=True)
        eq("--keep-vc names after the solution",
           os.path.exists(os.path.join(d, "max2-correct-vc.smt2")), True)

        # A wrong solution also leaves the counterexample query behind.
        bad = os.path.join(CASES, "max2-semantic-bad.out")
        cex = os.path.join(d, "cex.smt2")
        subprocess.run([sys.executable, TOOL, "--no-color", "--solver", solver,
                        bad, prob, "--vc-out", cex], capture_output=True, text=True)
        eq("--vc-out keeps the counterexample query",
           os.path.exists(os.path.join(d, "cex-cex.smt2")), True)
    return ok


def main():
    solver = os.environ.get("SYGUS_CHECK_SOLVER", "cvc5")
    ok = unit_tests() and option_tests(solver)
    failed = 0
    for sol, prob, extra, expect in TESTS:
        if not run_case(sol, prob, extra, expect, solver):
            failed += 1
    if not ok:
        failed += 1
    print("\n%d/%d integration cases passed" % (len(TESTS) - failed, len(TESTS)))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
