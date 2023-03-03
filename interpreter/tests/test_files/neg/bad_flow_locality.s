	mov r1 pc
	;; Cannot restrict Local to Global
	restrict r1 RWX LOCAL
	restrict r1 RWX GLOBAL
	halt
