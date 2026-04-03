(lang dune 3.21)
(using coq 0.8)
(warnings (deprecated_coq_lang disabled))

(package
 (name rocq-ol)
 (synopsis "Mechanization of Outcome Logic (OOPSLA 2023)")
 (allow_empty)
 (depends
  (coq-ext-lib (>= 0.12.0))))
