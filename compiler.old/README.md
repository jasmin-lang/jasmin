Installing with OPAM
====================

1. Switch to the jasmin directory.

2. Create a new opam switch for jasmin and activate it:

```
opam switch jasmin --alias-of 4.02.3
eval `opam config env`
```

3. Install all dependecies using opam:

```
opam pin add jasmin `pwd` -n
opam install jasmin --deps-only
```

4. Compile jasmin and test:

```
make jasmin
./scripts/run_tests.py
```

Documentation
=============

To build the jasmin documentation, you need the `Sphinx documentation
generator <http://www.sphinx-doc.org/>`_::

    $ pip install sphinx==1.3.5 sphinx-autobuild
    $ cd docs
    $ make html
    $ open _build/html/index.html

We have tested with version 1.3.5, but everything might also work with
a later version.

Hacking
=======

If you use emacs as an editor, then the following settings
might be useful:


(setq opam-share
      (substring
       (shell-command-to-string "opam config var share 2> /dev/null") 0 -1))
(add-to-list 'load-path (concat opam-share "/emacs/site-lisp"))
(require 'ocp-indent)
(require 'merlin)
;; Start merlin on ocaml files
(add-hook 'tuareg-mode-hook 'merlin-mode t)
;; Enable auto-complete
(setq merlin-use-auto-complete-mode 'easy)
;; Use opam switch to lookup ocamlmerlin binary
(setq merlin-command 'opam)
; Make company aware of merlin
(add-hook 'tuareg-mode-hook
          (lambda ()
            (set (make-local-variable 'company-backends)
                 '(merlin-company-backend))))

;; for folding sections marked with (* * TITLE *)
;; requires org-mode and outshine
(require 'outshine)
(add-hook 'outline-minor-mode-hook 'outshine-hook-function)
add-hook 'tuareg-mode-hook 'outline-minor-mode)


