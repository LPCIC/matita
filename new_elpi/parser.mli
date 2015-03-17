module Parser : sig
  type program
  type goal

  val parse_program : string -> program
  val parse_goal : string -> goal
end
