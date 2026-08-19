"""Minimal reader/printer for SMT-LIB v2 (and hence SyGuS v2) s-expressions.

Atoms are represented as ``str`` (holding the raw token text, so ``|foo bar|``
and ``"a string"`` keep their delimiters), lists as :class:`SList` (a ``list``
subclass that remembers the line it started on).
"""


class ParseError(Exception):
    pass


class SList(list):
    """A list of s-expressions, tagged with the source line it started on."""

    __slots__ = ("line",)

    def __init__(self, items=(), line=0):
        super().__init__(items)
        self.line = line


_WS = " \t\r\n\f\v"
_DELIM = _WS + '();|"'


def tokenize(text):
    """Yield ``(token, line)`` pairs.  Comments are dropped."""
    toks = []
    i, n, line = 0, len(text), 1
    while i < n:
        c = text[i]
        if c in _WS:
            if c == "\n":
                line += 1
            i += 1
        elif c == ";":
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif c in "()":
            toks.append((c, line))
            i += 1
        elif c == "|":
            j = text.find("|", i + 1)
            if j < 0:
                raise ParseError("line %d: unterminated quoted symbol" % line)
            toks.append((text[i:j + 1], line))
            line += text.count("\n", i, j)
            i = j + 1
        elif c == '"':
            j = i + 1
            while True:
                j = text.find('"', j)
                if j < 0:
                    raise ParseError("line %d: unterminated string literal" % line)
                if j + 1 < n and text[j + 1] == '"':  # "" is an escaped quote
                    j += 2
                    continue
                break
            toks.append((text[i:j + 1], line))
            line += text.count("\n", i, j)
            i = j + 1
        else:
            j = i
            while j < n and text[j] not in _DELIM:
                j += 1
            toks.append((text[i:j], line))
            i = j
    return toks


def parse(text):
    """Parse *text* into a list of top-level s-expressions."""
    toks = tokenize(text)
    out = []
    stack = []
    for tok, line in toks:
        if tok == "(":
            stack.append(SList([], line))
        elif tok == ")":
            if not stack:
                raise ParseError("line %d: unexpected ')'" % line)
            done = stack.pop()
            (stack[-1] if stack else out).append(done)
        else:
            (stack[-1] if stack else out).append(tok)
    if stack:
        raise ParseError("line %d: unterminated '('" % stack[-1].line)
    return out


def to_str(x):
    """Render an s-expression back to text on a single line."""
    if isinstance(x, list):
        return "(" + " ".join(to_str(y) for y in x) + ")"
    return x


def is_atom(x):
    return not isinstance(x, list)


def line_of(x, default=0):
    return getattr(x, "line", default)
