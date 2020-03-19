(* Abbreviations used in the address names below:
   A_{X} specifies the address of the symbol X
   -s and -e suffixes signify start and end, respectively, i.e. Xs is the start of X
   IO = MMIO Memory (currently just a single location)
   BC = Boot Code = code that initializes the read and write closures over the driver code, refines the omnipotent capability, and then passes control to an untrusted procedure that starts reading code through IO, that the adverary can later execute
   DC = Driver Code = the code for our driver, containing a read and a write method
   read, write = addresses of the read- and write routines of our driver
   RC = Read Code = the code that will read adversary code through IO, and store it in the adversary section AC of memory
   AC = Adversary Code = memory starting where the adversary code read through IO will be stored, running all the way to the end of physical memory

   TCB = Trusted Computing Base = Trusted Code = Boot Code + Driver Code
   UTCB = Untrusted Code = Memory - VC - IO = RC + AC
  *)

(* Starting configuration:
      All registers are empty, except for the PC register, which contains an omnipotent RWX capability for all of memory,
      hence including the MMIO location, and starts out pointing to A_BCs, the start of the boot code *)

(* Macros reused: *)

mclear, rclear

(* New Macros Used: *)

reqint r = (* Requires r to contain an integer. Implementation inspired by reqglob - we could also just have e.g. minus get stuck on a capability, but that might be a bit ugly? *)
    isptr r_t1 r
    lt r_t1 r_t1 1 (* Emulating boolean NOT *)
    move r_t2 pc
    lea r_t2 4 (* 4 is the offset to just after fail *)
    jnz r_t2 r_t1 (* Switched the order with respect to the tech-report; I think Lau made a typo here *)
    fail
    rclear {r_t1,r_t2}

lea_a r a = (* Absolute version of lea: set the value of the register r2, which should not be equal to the PC, to the hard-coded address A *)
    geta r_t1 r
    minus r_t1 a r_t1 (* Offset to first address *)
    lea r r_t1
    move r_t1 0

geq rres r1 r2 =
    lt rres r1 r2
    lt rres rres 1

(***** IO *****)
(* Memory location at A_IO = A_IOs = A_IOe, probably somewhere at the start of memory for convencience *)
(* This address can either be hard_coded into the program, or we could provide it as a parameter  *)

(***** BC *****)
(* We assume that the boot code contains the omnipotent capability in PC at the start of execution *)
(* Its goal is to jump to the first address of the adversary code (that can then start reading lines of code through IO), with in its registers the following values:
   * the PC contains a RWX capability that provides access to all of the adversaries memory; this way we do not need to create a separate capbility for the adversary code
   * r1 and r2 contain two enter capabilities to jump to the read and write routines of the driver, respectively  *)

(* Create closures for reading and writing through the driver *)
move r1 pc
subseg r1 A_DCs A_DCe
move r2 r1
lea_a r1 read
restrict r1 (encodePermPair (E,g))
lea_a r2 write
restrict r2 (encodePermPair (E,g))

(* Clear all of the adversary memory, in case we do not want to assume that it has either been zeroed or simply does not contain capabilities *)
(* Note that this does not include the adversary region RC, since we need the reading code to be there *)
gete r3 pc
move r0 pc
subseg r0 A_ACs r3
mclear r0

(* Prepare r0 with the region the adversary is allowed to have RWX control over, and have it point to the first address of this region *)
move r0 pc
subseg r0 A_RCs r3
lea_a r0 A_RCs

rclear RegName \ {r0,r1,r2,PC}
jmp r0


(***** DC *****)
(* Note: it does not seem to matter whether or not a stack is modeled, as no further calls happen and no local data needs to be stored outside of registers *)
(* Some memory address within the driver code has to contain a capability to access the MMIO location*)
A_DCs: <capability_for_memory> (* Capability for MMIO, with RW permission and range 1 *)
(* Arguments and return values for both functions are supposed to live in r1, whereas the return pointer is in r0 *)
read:   move r3 pc
        lea_a r3 A_DCs (* To make it point to the capability for MMIO *)
        load r2 r3
        load r1 r2
        rclear {r2,r3}
        jmp r0
write:  reqint r1 (* Macro defined above *)
        move r3 pc
        lea_a r3 A_DCs (* To make it point to the capability for MMIO *)
        load r2 r3
        store r2 r1
        rclear {r2,r3}
        jmp r0

(***** RC *****)
(* Piece of code that reads the adversary code through IO, this part can be untrusted*)

(* Move the read and write closures into safe caller registers, so that we do not overwrite them while reading *)
(* Optionally, we can move them back before jumping to the actual adversary code, but I do not do this yet *)
move r4 r1
move r5 r2

(* Set up all auxiliaries for the loop*)
jmp r4 (* N, the amount of lines to read, is now in r1 *)

(* Check that N>=1 *)
geq r6 r1 1
lea_a r7 N_IS_OK
jnz r7 r6
fail

N_IS_OK: lea_a r6 A_ACs
move r7 r1
move r0 pc
lea_a r0 loop (* Set up r0 so that it jumps to the loop, creating a do ... while loop *)

(* Now, we loop and read N lines using jnz *)
loop: jmp r4
      store r6 r1
      lea r6 1
      sub r7 1
      jnz r0 r7

(* Optionally, we could rearrange and clear registers here, but that is not strictly necessary *)

(***** AC *****)
(* The adversary code, read through IO, will be stored here, starting at address A_ACs. The rest of the memory also resides within this AC region, and can be used by the adversary in any way he sees fit. *)
