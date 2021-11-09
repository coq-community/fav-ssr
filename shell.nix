{ pkgs ? import <nixpkgs> {} }:
  pkgs.mkShell {
    # nativeBuildInputs is usually what you want -- tools you need to run
    nativeBuildInputs = [ 
			pkgs.gmp
			pkgs.coq
			pkgs.opam
			pkgs.ocaml
		];

		shellHook = '' 
			opam repo add coq-released https://coq.inria.fr/opam/released
			opam update
			opam install coq-equations
			opam install coq-mathcomp-ssreflect
			eval $(opam env)
		'';
}

