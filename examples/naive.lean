import Minimemo.Example.NaiveListener
open Memo Memo.NaiveListener

#eval (infer dom model).map (·.rows 4 3)
