    mov r0 stk                  ; r0 = (URWLX, Directed, b_stk, e_stk, b_stk)
    storeU stk 0 0
    promoteU stk
    lea stk (-1)                ; stk = (RWLX, Directed, b_stk, b_stk+1, b_stk)
    storeU r0 0 0
    storeU r0 0 0
    storeU r0 0 0               ; r0 = (URWLX, Directed, b_stk, e_stk, b_stk+3)
    ;; I cannot store r0 into stk, because r0 can _read_ up to b_stk+5,
    ;; so, it has to be store in a >= b_stk+3. But stk points to b_stk < b_stk+3
    store stk r0
    halt
