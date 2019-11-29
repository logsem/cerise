# Stratified capabilities[^1]

Assume capability machine with local and uninitialized capabilities:

- A capability is of the form `(p, l, b, e, a)` where
    + `p` is a permission, eg., `U`, `UL`, `E`, `RW`, `RWX`, `RWL`, `RWLX`
    + `l` is a locality, either `Global`, `StratifiedLocal` or `NonStratifiedLocal`[^2]
    + `b`, `e` and `a` are respectively the base, end and current addresses
- An uninitialized capability `(U, l, b, e, a)` is such that you get read-write-execute access between `b` and `a - 1`, and only write access between `a` and `e`
- An uninitialized capability `(UL, l, b, e, a)` is such that you get read-write-execute-local access between `b` and `a - 1`, and only write-local access between `a` and `e`
- A stratified capability `(p, StratifiedLocal, b, e, a)` is necessarily local, and is such that it can only be stored at an address `a'` if
    + `a ≤ a'` when `p` is either `U` or `UL`
    + `e < a` otherwise

Intuitively, owning a stack pointer `(UL, StratifiedLocal, b, e, a)` capability means that any capability having at least read permission over a range `[b', e'] ⊂ [b, e]` cannot have been derived from the aforementioned capability. Indeed, the capability is local, so a copy cannot be stored on the heap. It is also stratified, so a copy cannot be kept in lower level of the stack. Any copy is either outside or in the range `[b, e]` of the stack. In particular, this should mean that any caller never has access to the stack memory used by its descendants.

Conversely, using the same tricks as Lau's ESOP paper, a callee never has access to its ancestors's stack.

It should thus be possible to craft a calling convention such that Dead Store Elimination is made a secure optimization.

[^1]: Name subject to change, originally proposed by Thomas. Another proposition by Aïna is monotone capabilities.

[^2]: `NonStratifiedLocal` might not be useful for anything?
