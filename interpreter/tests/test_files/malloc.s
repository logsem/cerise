_init:
    mov r1 r31          ; r1 = (RWX, init, end, init)
	lea r1 (_malloc_bmid-init)	; r1 = (RWX, init, end, bmid)
	subseg r1 _malloc_bmid _malloc_end 	; r1 = (RWX, bmid, em, bmid)
    mov r2 r1           ; r2 = (RWX, init, end, bmid)
    lea r2 1            ; r2 = (RWX, init, end, am)
    store r1 r2         ; store the capability at bmid
    mov r2 0            ; clear r2
_end_init:
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
