	;; Init
	mov r1 pc             	; r1 = (RWX, init, end, init) 0
	lea r1 20	    	; r1 = (RWX, init, end, data) 1
	mov r2 r1             	; r2 = (RWX, init, end, data) 2
	lea r2 1              	; r2 = (RWX, init, end, data+1) 3
	store r2 2		; mem[data+1] <- 2 4
	store r1 r2           	; mem[data] <- (RWX, init, end, data+1) 5
	lea r1 (-9) 		; r1 = (RWX, init, end, code) 6
	subseg r1 11 21 	; r1 = (RWX, code, end, code) 7
	restrict r1 E 		; r1 = (E, code, end, code) 8
	mov r2 0 		; r2 = 0 9
	jmp r1   		; jump to unknown code: we only give it access 10

	;; Code
	mov r1 pc 		; r1 = (RX, code, end, code) 11
	lea r1 9		; r1 = (RX, code, end, data) 12
	load r1 r1		; r1 = (RWX, init, end, data+1) 13
	load r2 r1 		; r2 = <counter value> 14
	add r2 r2 1 		; r2 = <counter value>+1 15
	store r1 r2		; mem[data+1] <- <counter value>+1 16
	load r0 r1		; r0 = mem[data+1] 17
	mov r1 0		; r1 = 0 18
	halt 			; return to unknown code 19
	
	;; Data
	mov r5 r5 		; 20
	mov r5 0 		; 21
