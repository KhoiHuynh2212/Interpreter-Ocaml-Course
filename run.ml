let () =
  for i = 1 to 10 do
    let input_file  = "input/input"  ^ string_of_int i ^ ".txt" in
    let output_file = "output/output" ^ string_of_int i ^ ".txt" in
    Interpreter.interpreter (input_file, output_file)
  done