(lang dune 3.4)

(using menhir 2.1)

(name simple-analyzer)

(generate_opam_files true)

(source
 (github LimitEpsilon/simple-analyzer))

(authors "Joonhyup Lee")

(maintainers "Joonhyup Lee")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name simple-analyzer)
 (synopsis "Static analyzer for a simple imperative language.")
 (description "Static analyzer based on the abstract interpretation framework")
 (depends ocaml dune menhir)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
