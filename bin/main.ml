open L1terp

let e = L1Terp.Left (L1Terp.Bool false)

let _ = L1Terp.type_infer e
let _ = print_endline "Teste";