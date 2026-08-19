"""Parser for the candidate-solution file produced by a SyGuS solver.

The expected content is a sequence of ``define-fun`` commands, optionally
wrapped in a single pair of parentheses (the shape ``check-synth`` prints),
optionally preceded by a status atom such as ``sat`` or ``feasible``.
"""

from .sexpr import SList, line_of, parse, to_str


class SolutionError(Exception):
    pass


STATUS_ATOMS = {"sat", "unsat", "unknown", "feasible", "infeasible", "fail",
                "success", "unsupported"}

#: Answers that mean "no solution was produced".
NEGATIVE_STATUS = {"infeasible", "fail", "unknown", "unsat"}


class Definition:
    def __init__(self, name, args, ret, body, line=0):
        self.name = name
        self.args = args      # list of (name, sort)
        self.ret = ret
        self.body = body
        self.line = line

    def arg_sorts(self):
        return [s for _, s in self.args]

    def __str__(self):
        return to_str(SList(["define-fun", self.name,
                             SList([SList(a) for a in self.args]),
                             self.ret, self.body]))


class Solution:
    def __init__(self, defs, status=None, source=None):
        self.defs = defs               # ordered list of Definition
        self.by_name = {d.name: d for d in defs}
        self.status = status
        self.source = source

    @classmethod
    def from_file(cls, path):
        with open(path, "r") as f:
            sol = cls.from_string(f.read())
        sol.source = path
        return sol

    @classmethod
    def from_string(cls, text):
        top = parse(text)
        status = None
        while top and not isinstance(top[0], list):
            atom = top[0]
            if atom.lower() not in STATUS_ATOMS:
                raise SolutionError("unexpected atom %r at top level" % atom)
            status = atom.lower()
            top = top[1:]
        # Unwrap the outer parentheses of "( (define-fun ...) ... )".
        if len(top) == 1 and isinstance(top[0], list) and (
                not top[0] or isinstance(top[0][0], list)):
            top = list(top[0])
        defs = []
        for cmd in top:
            defs.append(_definition(cmd))
        if not defs and status is None:
            raise SolutionError("no definitions found")
        return cls(defs, status)


def _definition(cmd):
    if not isinstance(cmd, list) or not cmd:
        raise SolutionError("line %d: expected a define-fun, got %s"
                            % (line_of(cmd), to_str(cmd)))
    if cmd[0] != "define-fun":
        raise SolutionError("line %d: expected define-fun, got %r"
                            % (line_of(cmd), to_str(cmd[0])))
    if len(cmd) != 5 or not isinstance(cmd[2], list):
        raise SolutionError("line %d: malformed define-fun: %s"
                            % (line_of(cmd), to_str(cmd)))
    args = []
    for a in cmd[2]:
        if not isinstance(a, list) or len(a) != 2:
            raise SolutionError("line %d: malformed parameter %s"
                                % (line_of(cmd), to_str(a)))
        args.append((a[0], a[1]))
    return Definition(cmd[1], args, cmd[3], cmd[4], line_of(cmd))
