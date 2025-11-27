import ast


class AccessCollector(ast.NodeVisitor):
    def __init__(self):
        self.reads = []
        self.writes = []
        # Scope tracking could be complex, but for now we just grab all array accesses.
        # We treat Subscripts as array accesses.

    def visit_Subscript(self, node):
        # A[i]
        # node.value is the array (Name or Attribute)
        # node.slice is the index
        # node.ctx is Load or Store

        # We recursively visit the slice (index) first, because indices are READS
        # even if the subscript is a store. A[B[i]] = ... -> B[i] is read.
        old_reads = self.reads
        self.reads = []  # Temporarily capture index reads
        self.visit(node.slice)
        index_reads = self.reads
        self.reads = old_reads + index_reads

        access_str = ast.unparse(node)
        array_name = ast.unparse(node.value)
        dims = 1
        if isinstance(node.slice, ast.Tuple):
            dims = len(node.slice.elts)

        access_info = (array_name, dims, access_str)

        if isinstance(node.ctx, ast.Store):
            if access_info not in self.writes:
                self.writes.append(access_info)
        else:
            # Load or Del (Del not supported really)
            if access_info not in self.reads:
                self.reads.append(access_info)

        # We do NOT visit node.value (the array name) as a generic visit,
        # because we don't want to pick it up as a read variable if we were tracking scalars.
        # But since we only track Subscripts, visiting node.value (Name) doesn't trigger visit_Subscript.

    def visit_Call(self, node):
        # If there are nested calls, we should visit arguments.
        # If it's an 'op()' call, we might want to extract its declared reads/writes?
        # For mixed usage support.
        # For now, just generic recursion.
        self.generic_visit(node)


def get_accesses(nodes):
    """
    Returns (reads, writes) lists of tuples (name, dims, access_str) for the given list of AST nodes.
    """
    collector = AccessCollector()
    if isinstance(nodes, list):
        for node in nodes:
            collector.visit(node)
    elif isinstance(nodes, ast.AST):
        collector.visit(nodes)

    return collector.reads, collector.writes
