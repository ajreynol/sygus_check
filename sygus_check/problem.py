"""Parser for SyGuS v2 input files (https://sygus-org.github.io/language/)."""

from .sexpr import SList, line_of, parse, to_str
from .terms import substitute


class SygusError(Exception):
    pass


#: Commands copied verbatim into the generated SMT-LIB verification condition.
PREAMBLE_CMDS = {
    "declare-datatype", "declare-datatypes", "declare-sort", "define-sort",
    "define-fun", "define-funs-rec", "define-fun-rec", "declare-fun",
    "declare-const", "set-option",
}

#: Commands that carry no meaning for the check.
IGNORED_CMDS = {"set-info", "set-feature", "check-synth", "declare-weight",
                "set-logic"}

#: SyGuS 2.1 oracle / chc extensions we do not model.
UNSUPPORTED_CMDS = {
    "oracle-assume", "oracle-constraint", "declare-oracle-fun",
    "oracle-constraint-io", "oracle-constraint-cex", "oracle-constraint-membership",
    "oracle-constraint-poswitness", "oracle-constraint-negwitness",
    "oracle-assume-io", "chc-constraint", "optimization-synth",
}


class SortEnv:
    """Resolves ``define-sort`` aliases so sorts can be compared canonically."""

    def __init__(self):
        self.defs = {}  # name -> (params, body)

    def add(self, name, params, body):
        self.defs[name] = (list(params), body)

    def expand(self, s):
        if not isinstance(s, list):
            d = self.defs.get(s)
            if d is not None and not d[0]:
                return self.expand(d[1])
            return s
        if s and s[0] == "_":
            return s
        if s and not isinstance(s[0], list):
            d = self.defs.get(s[0])
            if d is not None and len(d[0]) == len(s) - 1:
                sub = dict(zip(d[0], [self.expand(a) for a in s[1:]]))
                return self.expand(substitute(d[1], sub))
        return SList([self.expand(a) for a in s])

    def canon(self, s):
        return to_str(self.expand(s))


class Grammar:
    def __init__(self, nts, sorts, rules, line=0):
        self.nts = nts            # ordered nonterminal names; nts[0] is the start
        self.sorts = sorts        # nt -> sort s-expression
        self.rules = rules        # nt -> list of grammar terms
        self.line = line

    @property
    def start(self):
        return self.nts[0]


class SynthFun:
    def __init__(self, name, args, ret, grammar, kind, line=0):
        self.name = name
        self.args = args          # list of (name, sort)
        self.ret = ret
        self.grammar = grammar    # Grammar or None
        self.kind = kind          # 'synth-fun' or 'synth-inv'
        self.line = line

    def arg_sorts(self):
        return [s for _, s in self.args]


class Problem:
    def __init__(self):
        self.logic = None
        self.sorts = SortEnv()
        self.preamble = []        # commands echoed into the SMT-LIB output
        self.synth = {}           # name -> SynthFun (insertion ordered)
        self.variables = []       # list of (name, sort) from declare-var
        self.constraints = []     # terms
        self.assumptions = []     # terms
        self.inv_constraints = [] # (inv, pre, trans, post)
        self.defined = {}         # name -> (arg sorts, ret sort) for define-fun
        self.source = None

    # -- parsing ---------------------------------------------------------
    @classmethod
    def from_file(cls, path):
        with open(path, "r") as f:
            text = f.read()
        p = cls.from_string(text)
        p.source = path
        return p

    @classmethod
    def from_string(cls, text):
        p = cls()
        for cmd in parse(text):
            p._command(cmd)
        return p

    def _err(self, cmd, msg):
        raise SygusError("line %d: %s: %s" % (line_of(cmd), msg, to_str(cmd)))

    def _command(self, cmd):
        if not isinstance(cmd, list) or not cmd:
            self._err(cmd, "not a command")
        head = cmd[0]
        if head == "set-logic":
            if len(cmd) != 2:
                self._err(cmd, "malformed set-logic")
            self.logic = cmd[1]
        elif head in ("synth-fun", "synth-inv"):
            self._synth_fun(cmd)
        elif head == "declare-var":
            if len(cmd) != 3:
                self._err(cmd, "malformed declare-var")
            self.variables.append((cmd[1], cmd[2]))
        elif head == "constraint":
            if len(cmd) != 2:
                self._err(cmd, "malformed constraint")
            self.constraints.append(cmd[1])
        elif head == "assume":
            if len(cmd) != 2:
                self._err(cmd, "malformed assume")
            self.assumptions.append(cmd[1])
        elif head == "inv-constraint":
            if len(cmd) != 5:
                self._err(cmd, "malformed inv-constraint")
            self.inv_constraints.append(tuple(cmd[1:5]))
        elif head in PREAMBLE_CMDS:
            if head == "define-sort":
                if len(cmd) != 4 or not isinstance(cmd[2], list):
                    self._err(cmd, "malformed define-sort")
                self.sorts.add(cmd[1], cmd[2], cmd[3])
            if head == "define-fun" and len(cmd) == 5 and isinstance(cmd[2], list):
                self.defined[cmd[1]] = ([a[1] for a in cmd[2]], cmd[3])
            self.preamble.append(cmd)
        elif head in IGNORED_CMDS:
            pass
        elif head in UNSUPPORTED_CMDS:
            self._err(cmd, "unsupported SyGuS command")
        else:
            self._err(cmd, "unknown command")

    def _synth_fun(self, cmd):
        kind = cmd[0]
        if kind == "synth-inv":
            if len(cmd) not in (3, 5):
                self._err(cmd, "malformed synth-inv")
            name, args, ret = cmd[1], cmd[2], "Bool"
            rest = list(cmd[3:])
        else:
            if len(cmd) not in (4, 6):
                self._err(cmd, "malformed synth-fun")
            name, args, ret = cmd[1], cmd[2], cmd[3]
            rest = list(cmd[4:])
        if not isinstance(args, list):
            self._err(cmd, "malformed argument list")
        arglist = []
        for a in args:
            if not isinstance(a, list) or len(a) != 2:
                self._err(cmd, "malformed argument %s" % to_str(a))
            arglist.append((a[0], a[1]))
        grammar = self._grammar(cmd, rest) if rest else None
        if name in self.synth:
            self._err(cmd, "duplicate function to synthesize %r" % name)
        self.synth[name] = SynthFun(name, arglist, ret, grammar, kind, line_of(cmd))

    def _grammar(self, cmd, rest):
        decls, groups = rest
        if not isinstance(decls, list) or not isinstance(groups, list):
            self._err(cmd, "malformed grammar")
        nts, sorts = [], {}
        for d in decls:
            if not isinstance(d, list) or len(d) != 2:
                self._err(cmd, "malformed nonterminal declaration %s" % to_str(d))
            if d[0] in sorts:
                self._err(cmd, "duplicate nonterminal %r" % d[0])
            nts.append(d[0])
            sorts[d[0]] = d[1]
        rules = {}
        for g in groups:
            if not isinstance(g, list) or len(g) != 3 or not isinstance(g[2], list):
                self._err(cmd, "malformed grouped rule list %s" % to_str(g))
            nt, sort, prods = g
            if nt not in sorts:
                self._err(cmd, "rule for undeclared nonterminal %r" % nt)
            if self.sorts.canon(sort) != self.sorts.canon(sorts[nt]):
                self._err(cmd, "sort mismatch for nonterminal %r" % nt)
            if nt in rules:
                self._err(cmd, "duplicate rule list for nonterminal %r" % nt)
            rules[nt] = list(prods)
        missing = [n for n in nts if n not in rules]
        if missing:
            self._err(cmd, "no productions for nonterminal(s) %s" % ", ".join(missing))
        return Grammar(nts, sorts, rules, line_of(cmd))

    # -- inv-constraint expansion ---------------------------------------
    def expanded_constraints(self, fresh_prefix="_sc"):
        """Return ``(constraints, extra_vars)``.

        ``inv-constraint`` commands are unfolded into the three standard
        implications over freshly declared state variables.
        """
        goals = list(self.constraints)
        extra = []
        for i, (inv, pre, trans, post) in enumerate(self.inv_constraints):
            f = self.synth.get(inv)
            if f is None:
                raise SygusError("inv-constraint refers to unknown function %r" % inv)
            xs, xps = [], []
            for j, (_, sort) in enumerate(f.args):
                x = "%s_%d_x%d" % (fresh_prefix, i, j)
                xp = "%s_%d_xp%d" % (fresh_prefix, i, j)
                xs.append(x)
                xps.append(xp)
                extra.append((x, sort))
                extra.append((xp, sort))
            app = lambda g, vs: SList([g] + list(vs)) if vs else g
            goals.append(SList(["=>", app(pre, xs), app(inv, xs)]))
            goals.append(SList(["=>", SList(["and", app(inv, xs),
                                             app(trans, xs + xps)]),
                                app(inv, xps)]))
            goals.append(SList(["=>", app(inv, xs), app(post, xs)]))
        return goals, extra
