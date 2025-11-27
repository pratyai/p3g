from .transpiler import PCodeTranspiler


def pcode(syms=None, decls=None, vars=None, outs=None):
    def decorator(func):
        try:
            transpiler = PCodeTranspiler(syms=syms, decls=decls, vars=vars, outs=outs)
            pcode_str = transpiler.transpile(func)

            # Attach a method to get the pcode string
            def get_pcode():
                return pcode_str

            func.pcode = get_pcode

        except Exception as e:
            print(f"Failed to transpile {func.__name__}: {e}")
            raise e

        return func

    return decorator
