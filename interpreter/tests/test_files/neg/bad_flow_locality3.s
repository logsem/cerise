	mov r1 pc
	;; Cannot restrict Directed to Global
	restrict r1 RWX Directed
	restrict r1 RWX GLOBAL
	halt
