import Lake
open Lake DSL

package StarForming where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.1"

/-- bipartite graphs whose upper k-star-forming number exceeds their k-independence number -/
@[default_target]
lean_lib StarForming
