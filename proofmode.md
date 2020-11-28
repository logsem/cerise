# Proofmode tactics and workflow

## Writing programs

Define a program as a concatenation of lists of instructions (encoded using
`encodeInstrsW`), and macro blocks. Example:

```coq
Definition assert_r_z_instrs f_a (r: RegName) (z: Z) :=
  fetch_instrs f_a ++
  encodeInstrsW [
    Sub r r z;
    Jnz r_t1 r;
    Mov r_t1 0
  ].
```

When writing concrete instructions, use directly the constructors. There are
coercions `Z → (Z + RegName)` and `RegName → (Z + RegName)` so one can write
e.g. `Mov r_t1 r_t2` and `Mov r_t1 0` (but a few more type annotations might be
required elsewhere, as with `r` and `z` above).

## Writing program specifications

- Use `codefrag a_first prog_instrs` for the SL assertion corresponding to
  having the instructions `prog_instrs` in memory starting at address `a_first`.
  (`codefrag` needs to be explicit, not hidden behind a definition for the
  tactics to work)

- Use `(a_first ^+ length prog_instrs)%a` for the address just at the end of the
  program's code (e.g. to describe the value of the `PC` in the post-condition).

- To describe the fact that the PC capability is valid for the range of the
  program (replacing the use of `isCorrectPC_range`):
  + require `ExecPCPerm pc_p` (says that `pc_p` is `RX` or `RWX`)
  + require `SubBounds pc_b pc_e a_first (a_first ^+ length prog_instrs)%a`
    (says that the range of the program addresses is included in `[pc_b,pc_e)`)

## Proving specifications

The general idea is: given a program of the form `block1 ++ block2 ++ block2`,
focus each sub-block individually. Then, a sub-block is either a list of
concrete instructions, or a macro (for which we have a specification).

### Focusing a sub-block

Assuming we have `"Hprog" : codefrag a_first (block1 ++ block2 ++ ...)`:

- To focus the first sub-block, use `focus_block_0 "Hprog" as "Hblock" "Hcont"`.
  This will turn the `codefrag` in `"Hprog"` as a `codefrag` for the first block
  in `"Hblock"` (`"Hcont"` accounting for the remaining resources; as a magic
  wand).

- To focus the nth (with n >= 1, counting from 0) sub-block, use `focus_block n
  "Hprog" as a_mid Ha_mid "Hblock" "Hcont"`. This produces `"Hblock"` with a
  `codefrag` for the block, and introduces `amid`, the starting address of the
  block, and `Ha_mid` which specifies the offset between `a_mid` and `a_first`.

- To unfocus the current block and get back the assertion for the complete
  program, use `unfocus_block "Hblock" "Hcont" as "Hprog"`.

The focus tactics assume that the block structure (with the `++`) is explicit in
`"Hprog"`; that usually means first unfolding the `prog_instrs` definition
there.

The `focus_block` tactics also introduce some facts in the context about the
focused block, to help the automation. These are later removed by
`unfocus_block` to avoid cluttering the goal. Currently, those facts are
`ContiguousRegion` and `SubBounds` for the focused block (they help with proving
the address arithmetic side-conditions).

### When the whole program is a single block of instructions

When the whole program is a list of concrete instructions, one needs to manually
introduce the automation-helping "facts" before reasoning on the instructions
themselves (as described next). This is done by calling `codefrag_facts
"Hprog"`.

### Reasoning on a list of concrete instructions

Assuming we have `"Hblock" : codefrag a_first (encodeInstrsW [...])`:

- `iInstr "Hprog"` steps through one instruction.
 
  It will:
  + Lookup up PC, assuming its address is of the form `(a_first ^+ n)%a`.
  + Look up the `n`th instruction in `"Hblock"`.
  + Find the corresponding rule(s) for that instruction. Note that, just knowing
    the instruction, there may be more than one possible rule, so the tactic
    will try and backtrack if framing later fails. This can lead to unfortunate
    error messages, when the "correct" rule fails for a different reason, then
    the tactic backtracks to a different rule, then prints the error message for
    that rule…
  + NB: on `Jnz`, the tactic will assume that the condition is non-zero unless
    it syntactically matches 0. Thus, if it doesn't, one needs to rewrite it to
    zero before calling the tactic.
  + The tactic then instantiates the lemma and proves its precondition by
    syntactically framing points-to from the context, and proving pure
    side-conditions.

- `iGo "Hprog"` steps through as many instructions as possible, until a
  side-condition needs to be proven manually.

### Using the specification of a macro

Assuming we have `"Hblock" : codefrag a_first macro_instrs`:

Call `iApply macro_spec; iFrameCapSolve.`

The `iFrameCapSolve` tactic (also used internally by `iInstr`) will attempt to
frame resources and prove side-conditions as much as possible.

## Other useful tactics

- `solve_pure`: solves a pure side-condition related to capabilities or "easy"
    bound checking. Expected to succeed or fail fast.

- `solve_addr`: `lia`-like decision procedure for address arithmetic. Also
  handles some of the bound-checking related auxiliary definitions. Slower.

- `solve_pure_addr`: like `solve_pure`, but can also call `solve_addr` itself to
  solve address arithmetic. Slower, for interactive proofs.

- `iFrameCap`: try to frame a resource from the goal using the Iris context.
  Currently handles register and memory points-to and `codefrag`.

- `iFrameCapSolve`: multi-goal tactic, that repeats and combines `iFrameCap` and
  `solve_pure`.

- `wp_instr`, `wp_pure`, `wp_end`: administrative reduction steps for WP.
  `wp_instr`: before applying an instruction rule (automatically called by
  `iInstr`); `wp_pure`: after applying an instruction rule (automatically called
   by `iInstr`); `wp_end`: when the execution stopped (on fail/halt).

- `changePCto a`: change the current address of pc to `a`. Uses `solve_addr` to
  prove that the current addres is indeed equal to `a`.


## Understanding and debugging the tactics

- `iInstr "Hprog"` (in `proofmode.v`) is roughly equivalent to calling:

  + `iInstr_lookup "Hprog" as "Hi" "Hcont"` to access the points-to to the
    current instruction;
  
  + `iInstr_get_rule "Hi" (fun rule => ...)` to query the wp-rule(s) for the
    instruction. Its second argument is a tactic continuation. E.g. use
    `iInstr_get_rule "Hi" (fun rule => idtac rule)` to print the rules found.

  + `wp_instr`
  
  + `iApplyCapAuto rule` to apply the rule lemma and perform automatically
    framing/solving;
  
  + `iDestruct ("Hcont" with "Hi") as "Hprog""` to recover the codefrag for the
    whole block;
  
  + `wp_pure`

- `iApplyCapAuto rule` (in `proofmode.v`) is roughly equivalent to:

  + `iApplyCapAuto_init rule` to apply the rule in "frame inference" mode;
  
  + `all: iFrameCapSolve` to frame resources and solve side conditions
  
  + `iNamedAccu` to collect the remaining context and pass it to the second
    subgoal. This can fail at this point if there are remaining resources
   (i.e. we couldn't completely instantiate the lemma precondition).

  + `iNamedIntro` to reintroduce the context in the other subgoal.

  + `iNext; iIntros "..."` to reintroduce the relevant resources with the
    same names as before.

- `iFrameCapSolve` calls `iFrameCap` and `solve_cap_pure` on all goals in a
  loop (see `proofmode.v`).

- `solve_pure`: see `solve_pure.v`
- `solve_addr`: see `solve_addr.v` and `solve_addr_extra.v`
