  mov r1 pc             ; r1 = (RWX, init, end, init)
  lea r1 (80-20)    ; r1 = (RWX, init, end, data)
  mov r2 r1             ; r2 = (RWX, init, end, data)
  lea r2 1              ; r2 = (RWX, init, end, data+1)
  store r1 r2           ; mem[data] <- (RWX, init, end, data+1)
  lea r1 (80-35) ; r1 = (RWX, init, end, code)
  subseg r1 35 100 ; r1 = (RWX, code, end, code)
  restrict r1 E ; r1 = (E, code, end, code)
  mov r2 0 ; r2 = 0
  jmp r0   ; jump to unknown code: we only give it access
