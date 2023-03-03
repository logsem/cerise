	mov r1 pc
	;; Cannot restrict Directed to Local
	restrict r1 RWX Directed
	restrict r1 RWX Local
	halt
