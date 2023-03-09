#!/usr/bin/env python3
import sys
import os

def parse_component(input_file, name_component):
    f=open(input_file, "rt")
    lines = f.readlines()
    lines = [ l.strip() for l in lines ]

    start_init=0
    end_init=0
    i=0
    # Skip until the init part
    while lines[i] != "_init:": i+=1
    start_init = i
    # Skip until the end of the init part
    while lines[i] != "_end_init:": i+=1
    i+=1
    end_init = i

    init_code = lines[start_init:end_init]

    start_prog=0
    end_prog=0
    # Skip until the program part
    while lines[i] != "_"+name_component+":": i+=1
    start_prog=i
    # Skip until the end of the program part
    while lines[i] != "_"+name_component+"_end:": i+=1
    i+=1
    end_prog=i

    prog_code = lines[start_prog:end_prog]

    return (init_code, prog_code)

def init_linking_table(renv, rlt, slt, elt, init):
    prog_init=[f"{init}:",
               f"mov {renv} pc",
               f"mov {rlt} {renv}",
               f"lea {rlt} ({slt}-{init})",
               f"subseg {rlt} {slt} {elt}"]
    return ("\n\t".join(prog_init))


def create_closure(renv1, renv31, label_start, label_end, init):
    prog_closure=[
        f"mov {renv1} {renv31}",
        f"lea {renv1} ({label_start}-{init})",
	    f"subseg {renv1}  {label_start} {label_end}",
        f"restrict {renv1} E GLOBAL",
    ]
    return ("\n\t".join(prog_closure))

def store_closure(i, rlt, rcls):
    store_cls_instr=[
        f"lea {rlt} {i}",
        f"store {rlt} {rcls}",
        f"lea {rlt} -{i}"
    ]
    return ("\n\t".join(store_cls_instr))

def create_closure_code(rcls, renv, rlt, start_label, end_label, code_label, init):
    prog_closure=[
        f"mov {rcls} {renv}",
        f"lea {rcls} ({start_label}-{init})",
        f"store {rcls} {rlt}",
        f"lea {rcls} ({code_label}-{start_label})",
        f"subseg {rcls} {start_label} {end_label}",
        f"restrict {rcls} E GLOBAL"
    ]
    return ("\n\t".join(prog_closure))


def clear_registers():
   return ""

def insert_linking_table(components, slt, elt):
    prog_lt=[slt+":\n\t"]
    for component in components:
        component_name,_ = os.path.splitext(os.path.basename(component))
        prog_lt.append(f"jmp pc ; dummy data, entry {component_name}\n\t")
    prog_lt.append(elt+":\n\t")
    return "\n\t".join(prog_lt)

def link_program(components, code, renv, rlt, slt, elt, rcls, rcls_code, init):
    prog=""
    prog += init_linking_table(renv, rlt, slt, elt, init)
    i=0
    for component in components:
        component_name,_ = os.path.splitext(os.path.basename(component))
        (init_component, prog_component) = parse_component(component,
                                                           component_name)
        prog+=f"\n\n; init {component_name}\n\t"
        prog += "\n\t".join(init_component[1:-1])
        prog+=f"\n; closure {component_name}\n\t"
        prog += create_closure(rcls, renv, "_"+component_name,
                               "_"+component_name+"_end", init)
        prog+="\n\t"
        prog += store_closure(i, rlt, rcls)
        i+=1
    # restrict capability and points to the first entry of the table
    prog+=f"\n\trestrict {rlt} RO GLOBAL\n\t"

    prog+=f"\n; closure code\n\t"
    # closure for the code
    prog+= create_closure_code(rcls_code, renv, rlt, "data", "end", "code", init )
    # clear registers
    prog+= clear_registers()
    prog+= f"\n\tjmp {rcls_code}\n\t"
    prog+="\n; code prog \n\t"
    prog+=code

    prog+="\n; linking table \n\t"
    prog+=insert_linking_table(components, slt, elt)


    for component in components:
        component_name,_ = os.path.splitext(os.path.basename(component))
        (init_component, prog_component) = parse_component(component,
                                                           component_name)
    prog+=f"\n; {component_name} prog \n\t"
    prog+= "\n\t".join(prog_component)

    return prog


# TODO being able to replace macros (fetch, malloc, etc)

if __name__ == '__main__':
    program_file = sys.argv[1]
    components = sys.argv[2:]

    f=open(program_file, "rt")
    program_code = f.readlines()
    code = "".join(program_code)

    renv="r31"
    rlt="r30"
    rcls="r3"
    rcls_code="r4"
    slt="_start_lt"
    elt="_end_lt"
    init="init"
    print(link_program(components, code, renv, rlt, slt, elt, rcls, rcls_code, init))
