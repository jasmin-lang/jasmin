Installing with OPAM
====================

1. Switch to the dmasm directory.

2. Create a new opam switch for dmasm and activate it:

```
opam switch dmasm --alias-of 4.02.3
eval `opam config env`
```

3. Install all dependecies using opam:

```
opam pin add dmasm `pwd` -n
opam install dmasm --deps-only
```

4. Compile dmasm and test:

```
make dmasm
make test-dmasm-square # output assembly file
make unit-tests
```

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


