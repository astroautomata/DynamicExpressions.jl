namespace DynExpr

/-- Julia exceptions used by the package: src/Utils.jl:67,
src/ValueInterface.jl:39, src/Node.jl:351, and src/ExtensionInterface.jl:27.
`undefinedBehavior` records invalid unchecked accesses rather than assigning a value. -/
inductive JlError where
  | boundsError
  | undefRefError
  | assertionError (msg : String)
  | argumentError (msg : String)
  | domainError (msg : String)
  -- Julia Base v1.12.0, base/array.jl:12-15.
  | dimensionMismatch (msg : String)
  -- Julia Core, base/boot.jl:422-426, modeled at the exception-type level.
  | inexactError
  | methodError (msg : String)
  | errorException (msg : String)
  | undefinedBehavior (msg : String)
  | userError (msg : String)
  deriving Repr, DecidableEq

/-- Explicit exception results for Julia calls, including src/Utils.jl:67
and src/ValueInterface.jl:39. -/
abbrev Jl := Except JlError

end DynExpr
