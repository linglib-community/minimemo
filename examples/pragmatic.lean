import Minimemo.Example.PragmaticListener
open Memo Memo.PragmaticListener

#eval (infer NaiveListener.dom model).map (·.rows 4 3)
