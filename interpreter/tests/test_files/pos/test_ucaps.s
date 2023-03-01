    storeU stk 0 1
    storeU stk 0 43
    storeU stk (-2) 42

    loadU r0 stk -2
    loadU r1 stk -1
    mov r2 stk
    promoteU r2
    halt
