{
  open Parser
}

rule token = parse
| eof { EOF }

{ }
