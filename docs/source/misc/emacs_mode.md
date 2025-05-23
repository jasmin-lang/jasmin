# Emacs mode

Poor’s man lexical highlighting in Emacs can be achieved by the following command in your `.emacs`:

~~~
  ;; Jasmin
  (require 'generic-x)
  (define-generic-mode
      'jasmin-mode ; name
    '("//" ("/*" . "*/")) ; comments
    '("param" "fn" "inline" "export" "reg" "stack" "global" "int" "bool" "u8" "u16" "u32" "u64" "u128" "u256"
      "from" "require"
      "return" "ptr" "const" "mut"
      "while" "for" "to" "downto") ; keywords
    '(("#\\(if\\(def\\)?\\|else\\|endif\\).*$" . 'font-lock-preprocessor-face)
      ("\\(if\\|else\\)" . 'font-lock-keyword-face)
      ("#[a-zA-Z_][a-zA-Z_0-9]*" . 'font-lock-builtin-face)
      ("\\b[0-9]+\\b" . 'font-lock-constant-face)
      ); font-lock
    '("\\.jazz$" "\\.japp$" "\\.jinc$"); file names
    '()
    "Not A Jasmin Mode"
    )
~~~
