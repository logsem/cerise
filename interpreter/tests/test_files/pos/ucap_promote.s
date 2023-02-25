	;; Init
	mov r0 stk
	mov r1 stk
	mov r2 stk
	mov r3 stk
    promoteU r0
    restrict r1 URWL LOCAL
    promoteU r1
    restrict r2 URWX LOCAL
    promoteU r2
    restrict r3 URW LOCAL
    promoteU r3
    halt
