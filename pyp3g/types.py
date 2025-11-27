class P3GObject:
    pass


class Symbol(P3GObject):
    def __init__(self, name):
        self.name = name

    def __add__(self, other):
        return self

    def __sub__(self, other):
        return self

    def __mul__(self, other):
        return self

    def __truediv__(self, other):
        return self

    def __lt__(self, other):
        return self

    def __le__(self, other):
        return self

    def __gt__(self, other):
        return self

    def __ge__(self, other):
        return self

    # Add __index__ to allow Symbol objects in range() without type warnings
    def __index__(self):
        return 0  # Dummy value, as actual execution is not intended


class Variable(Symbol):
    pass


class Array(P3GObject):
    def __init__(self, name):
        self.name = name

    def __getitem__(self, item):
        return self

    def __setitem__(self, key, value):
        pass


def sym(*names):
    pass


def decl(*names):
    pass


def var(*names):
    pass


def out(*names):
    pass


def op(desc=None, reads=None, writes=None, label=None):
    pass


def assertion(condition):
    pass
