"""Term utilities: binders, substitution, let-expansion and literal recognition."""

import re

from .sexpr import SList, to_str

#: Binders whose first argument is a list of ``(symbol sort)`` pairs.
SORTED_BINDERS = ("forall", "exists", "lambda")

NUMERAL_RE = re.compile(r"^[0-9]+$")
DECIMAL_RE = re.compile(r"^[0-9]+\.[0-9]+$")
HEX_RE = re.compile(r"^#x[0-9a-fA-F]+$")
BIN_RE = re.compile(r"^#b[01]+$")
STRING_RE = re.compile(r'^".*"$', re.S)
BV_LIT_RE = re.compile(r"^bv[0-9]+$")

ROUNDING_MODES = {
    "RNE", "RNA", "RTP", "RTN", "RTZ",
    "roundNearestTiesToEven", "roundNearestTiesToAway",
    "roundTowardPositive", "roundTowardNegative", "roundTowardZero",
}


def literal_sorts(t):
    """Return the possible sorts (as canonical strings) of *t* if it is a
    literal constant, else ``None``.

    A numeral is reported as both ``Int`` and ``Real`` because in a logic with
    reals ``1`` is a legal real constant.  Negated numerals such as ``(- 1)``
    count as constants too, since that is how solvers print them.
    """
    if isinstance(t, list):
        if len(t) == 2 and t[0] == "-":
            return literal_sorts(t[1])
        if len(t) == 3 and t[0] == "/":
            a, b = literal_sorts(t[1]), literal_sorts(t[2])
            if a and b and "Real" in a and "Real" in b:
                return ["Real"]
            return None
        # (_ bvN m), (_ +zero e s), ...
        if len(t) >= 3 and t[0] == "_":
            if BV_LIT_RE.match(str(t[1])) and NUMERAL_RE.match(str(t[2])):
                return ["(_ BitVec %s)" % t[2]]
            if t[1] in ("+zero", "-zero", "+oo", "-oo", "NaN") and len(t) == 4:
                return ["(_ FloatingPoint %s %s)" % (t[2], t[3])]
        return None
    if t in ("true", "false"):
        return ["Bool"]
    if t in ROUNDING_MODES:
        return ["RoundingMode"]
    if NUMERAL_RE.match(t):
        return ["Int", "Real"]
    if DECIMAL_RE.match(t):
        return ["Real"]
    if HEX_RE.match(t):
        return ["(_ BitVec %d)" % (4 * (len(t) - 2))]
    if BIN_RE.match(t):
        return ["(_ BitVec %d)" % (len(t) - 2)]
    if STRING_RE.match(t):
        return ["String"]
    return None


def is_literal(t):
    return literal_sorts(t) is not None


def free_symbols(t, acc=None):
    """All atoms occurring in *t* that are not in head/binder position.

    This is deliberately coarse: it is used only to avoid variable capture.
    """
    if acc is None:
        acc = set()
    if not isinstance(t, list):
        acc.add(t)
        return acc
    for x in t:
        free_symbols(x, acc)
    return acc


def _fresh(name, avoid):
    i = 0
    new = name
    while new in avoid:
        i += 1
        new = "%s!%d" % (name, i)
    return new


def substitute(t, sub):
    """Capture-avoiding simultaneous substitution of symbols by terms."""
    if not sub:
        return t
    if not isinstance(t, list):
        return sub.get(t, t)
    if t and t[0] == "let" and len(t) == 3 and isinstance(t[1], list):
        bindings = [[b[0], substitute(b[1], sub)] for b in t[1]]
        inner = dict(sub)
        for b in t[1]:
            inner.pop(b[0], None)
        bound = {b[0] for b in t[1]}
        return _rebind(t, bindings, bound, inner, sub, let=True)
    if t and t[0] in SORTED_BINDERS and len(t) == 3 and isinstance(t[1], list):
        inner = dict(sub)
        for b in t[1]:
            inner.pop(b[0], None)
        bound = {b[0] for b in t[1]}
        return _rebind(t, [list(b) for b in t[1]], bound, inner, sub, let=False)
    return SList([substitute(x, sub) for x in t], getattr(t, "line", 0))


def _rebind(t, bindings, bound, inner, sub, let):
    """Shared tail of :func:`substitute` for the two binder shapes."""
    incoming = set()
    for k, v in inner.items():
        incoming |= free_symbols(v)
    clash = bound & incoming
    if clash:
        avoid = incoming | free_symbols(t[2]) | bound
        ren = {}
        for b in bindings:
            if b[0] in clash:
                nw = _fresh(b[0], avoid)
                avoid.add(nw)
                ren[b[0]] = nw
                b[0] = nw
        body = substitute(t[2], ren)
    else:
        body = t[2]
    return SList([t[0], SList([SList(b) for b in bindings]), substitute(body, inner)],
                 getattr(t, "line", 0))


def expand_lets(t):
    """Eliminate every ``let`` by substituting its (already expanded) bindings.

    Solvers routinely print solutions with ``let`` abbreviations; the grammar
    check needs the unfolded term.
    """
    if not isinstance(t, list):
        return t
    if t and t[0] == "let" and len(t) == 3 and isinstance(t[1], list):
        sub = {b[0]: expand_lets(b[1]) for b in t[1]}
        return expand_lets(substitute(t[2], sub))
    return SList([expand_lets(x) for x in t], getattr(t, "line", 0))


def strip_annotations(t):
    """Drop ``(! t :attr ...)`` wrappers."""
    if not isinstance(t, list):
        return t
    if t and t[0] == "!" and len(t) >= 2:
        return strip_annotations(t[1])
    return SList([strip_annotations(x) for x in t], getattr(t, "line", 0))


def key(t):
    """Hashable canonical key for a term."""
    return to_str(t)
