import Lake
open Lake DSL

package «eml-formal» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Eml» where
  roots := #[`Eml]
