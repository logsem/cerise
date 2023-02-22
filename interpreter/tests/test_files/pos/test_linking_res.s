init:
	mov r31 pc
	mov r30 r31
	lea r30 (_start_lt-init)
	subseg r30 _start_lt _end_lt

; init malloc
	mov r1 r31          ; r1 = (RWX, init, end, init)
	lea r1 (_malloc_bmid-init)	; r1 = (RWX, init, end, bmid)
	subseg r1 _malloc_bmid _malloc_end 	; r1 = (RWX, bmid, em, bmid)
	mov r2 r1           ; r2 = (RWX, init, end, bmid)
	lea r2 1            ; r2 = (RWX, init, end, am)
	store r1 r2         ; store the capability at bmid
	mov r2 0            ; clear r2
; closure malloc
	mov r1 r31
	lea r1 (_malloc-init)
	subseg r1  _malloc _malloc_end
	restrict r1 E
	lea r30 0
	store r30 r1
	lea r30 -0
	restrict r30 RO
	
; closure code
	mov r0 r31
	lea r0 (data-init)
	store r0 r30
	lea r0 (code-data)
	subseg r0 data end
	restrict r0 E
	jmp r0
	
; code prog 
	data:
    jmp pc                      ; dummy data, for linking_table
code:
    mov r0 0                     ; for linking_table
    ;; allocation of buffer
    ;; 1) fetch
    mov r1 pc
    getb r2 r1
    geta r3 r1
    sub r2 r2 r3
    lea r1 r2
    load r1 r1
    lea r1 0                    ; entry of malloc = 0
    mov r2 0
    mov r3 0
    load r1 r1
    ;; 2) call malloc
    mov r5 r0
    mov r3 r1
    mov r1 5                 ; size of allocation
    mov r0 pc
    lea r0 3
    jmp r3
    mov r0 r5
    mov r5 0
    ;; use the allocated memory
    store r1 1
    lea r1 1
    store r1 2
    lea r1 1
    store r1 3
    lea r1 1
    store r1 4
    lea r1 1
    store r1 5
    mov r31 r1                  ; copy the capability to the 1st buffer

    ;; allocation another buffer
    ;; 1) fetch
    mov r1 pc
    getb r2 r1
    geta r3 r1
    sub r2 r2 r3
    lea r1 r2
    load r1 r1
    lea r1 0                    ; entry of malloc = 0
    mov r2 0
    mov r3 0
    load r1 r1
    ;; 2) call malloc
    mov r5 r0
    mov r3 r1
    mov r1 3                 ; size of allocation 3
    mov r0 pc
    lea r0 3
    jmp r3
    mov r0 r5
    mov r5 0

    ;; use assert to check idk ?

    halt
end:

; linking table 
	_start_lt:
	
	jmp pc ; dummy data, entry malloc
	
	_end_lt:
	
; malloc prog 
	_malloc:
	lt r3 0 r1
	mov r2 pc
	lea r2 4
	jnz r2 r3
	fail
	mov r2 pc
	lea r2 21 ; size subroutine
	load r2 r2
	geta r3 r2
	lea r2 r1
	geta r1 r2
	mov r4 r2
	subseg r4 r3 r1
	sub r3 r3 r1
	lea r4 r3
	mov r3 r2
	sub r1 0 r1
	lea r3 r1
	getb r1 r3
	lea r3 r1
	store r3 r2
	mov r1 r4
	mov r2 0
	mov r3 0
	mov r4 0
	jmp r0
	_malloc_bmid:
	jmp pc                    ; dummy data, for capabilibity (RWX, bmid, em, a)
	_malloc_am:
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	jmp pc ; dummy data
	_malloc_end:
