    mov r0 stk                  ; r0 = (URWLX, Directed, b_stk, e_stk, b_stk)
    mov r1 stk                  ; r1 = (URWLX, Directed, b_stk, e_stk, b_stk)
    storeU r1 0 0
    storeU r1 0 0
    storeU r1 0 0
    storeU r1 0 0
    storeU r1 0 0
    promoteU r1
    lea r1 (-1)                 ; r1 = (RWLX, Directed, b_stk, b_stk+5, b_stk+4)
    storeU r0 0 0               ; r0 = (URWLX, Directed, b_stk, e_stk, b_stk+1)

    ;; I can store r0 in r1, because r0 can read up to b_stk+1 < b_stk+4
    store r1 r0
    lea r1 (-1)                 ; r1 = (RWLX, Directed, b_stk, b_stk+5, b_stk+3)
    promoteU r0                 ; r0 = (RWLX, Directed, b_stk, b_stk+1, b_stk+1)
    ;; I can store r0 in r1, because r0 can read up to b_stk+1 < b_stk+3
    store r1 r0


    storeU stk 0 0
    storeU stk 0 0
    storeU stk 0 0
    storeU stk 0 0
    storeU stk 0 0              ; stk = (URWLX, Directed, b_stk, e_stk, b_stk+4)

    ;; I can store r0 in stk, because r0 can read up to (b_stk+1) and b_stk+1 <= (b_stk+3)
    storeU stk (-1) r0

    halt
