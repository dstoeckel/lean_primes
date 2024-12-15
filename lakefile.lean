import Lake
open Lake DSL

package "primes" where
  -- add package configuration options here

lean_lib «Primes» where
  -- add library configuration options here

@[default_target]
lean_exe "primes" where
  root := `Main
