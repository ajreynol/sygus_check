"""Top-level orchestration: signature, syntactic and semantic checks."""

from . import semantic, syntactic
from .sexpr import to_str


class Report:
    def __init__(self):
        self.signature = []     # list of (level, message); level in 'error'/'warning'
        self.syntactic = []     # list of SyntacticResult
        self.semantic = None    # SemanticResult or None
        self.status = "correct"

    def note(self, level, msg):
        self.signature.append((level, msg))
        if level == "error":
            self.status = "incorrect"

    def finish(self):
        if self.status == "incorrect":
            return self.status
        for r in self.syntactic:
            if r.status == "violation":
                self.status = "incorrect"
                return self.status
        if any(r.status == "inconclusive" for r in self.syntactic):
            self.status = "unknown"
        if self.semantic is not None:
            if self.semantic.status == "incorrect":
                self.status = "incorrect"
            elif not self.semantic.ok and self.status != "incorrect":
                self.status = "unknown"
        return self.status


def check_signatures(problem, solution, report):
    """Check that the solution defines exactly the functions to synthesize."""
    canon = problem.sorts.canon
    for name, sf in problem.synth.items():
        d = solution.by_name.get(name)
        if d is None:
            report.note("error", "no definition given for %s %s"
                        % (sf.kind, name))
            continue
        if len(d.args) != len(sf.args):
            report.note("error", "%s: expected %d parameter(s), solution has %d"
                        % (name, len(sf.args), len(d.args)))
            continue
        for i, ((_, ds), (an, ss)) in enumerate(zip(d.args, sf.args)):
            if canon(ds) != canon(ss):
                report.note("error",
                            "%s: parameter %d (%s) has sort %s, expected %s"
                            % (name, i + 1, an, to_str(ds), to_str(ss)))
        if canon(d.ret) != canon(sf.ret):
            report.note("error", "%s: return sort is %s, expected %s"
                        % (name, to_str(d.ret), to_str(sf.ret)))
    for d in solution.defs:
        if d.name not in problem.synth:
            report.note("warning", "solution defines %s, which the problem does "
                        "not ask to synthesize" % d.name)


def run(problem, solution, do_syntactic=True, do_semantic=True, **semopts):
    report = Report()
    if solution.status in ("infeasible", "fail", "unknown", "unsat"):
        report.note("error", "solver reported %r: no solution to check"
                    % solution.status)
        report.finish()
        return report
    check_signatures(problem, solution, report)
    if report.status == "incorrect":
        report.finish()
        return report
    if do_syntactic:
        for name, sf in problem.synth.items():
            d = solution.by_name[name]
            report.syntactic.append(syntactic.check(sf, d, problem.sorts))
    if do_semantic:
        report.semantic = semantic.check(problem, solution, **semopts)
    report.finish()
    return report
