;; Syntax hightlighting and indentation for Kami code.
;; Author : Murali Vijayaraghavan
;; Organization : SiFive

(defvar kami-keywords
  '(
    "MODULE"
    "MOD"
    "Register"
    "Rule"
    "Method"
    "Call"
    "LET"
    "LETA"
    "LETE"
    "LETC"
    "RetE"
    "Read"
    "Write"
    "Assert"
    "NonDet"
    "IF"
    "If"
    "then"
    "else"
    "Retv"
    "Ret"
    "with"
    "MODULE_WF"
    "MOD_WF"
    )
  )

(defvar kami-types-and-vals
  '(
    "Bool"
    "Bit"
    "STRUCT"
    "Array"
    "Default"
    "WO"
    )
  )

(defvar kami-keywords-regex (regexp-opt kami-keywords 'words))
(defvar kami-types-and-vals-regex (regexp-opt kami-types-and-vals 'words))

(defvar kami-font-lock-keywords
  `(
    (,kami-keywords-regex . font-lock-keyword-face)
    (,kami-types-and-vals-regex . font-lock-builtin-face)
    )
  )

(defun diffParensPlusInit ()
  "Searches backwards for the first occurence of MODULE {.
   Calculates the number of open parentheses minus closed parentheses,
   and adds that to the starting point of
   MODULE {"
  (save-excursion
    (beginning-of-line)
    (let ((curr (point)))
      (re-search-backward "MODULE[ \t\r\n\v\f]*{")
      (let ((init (point)))
	(beginning-of-line)
	(max (+ (* 2 (- (how-many "[[({]" init curr)
			(how-many "[])}]" init curr)
			)
		   (- init (- (point) 1))
		   )
		0
		)
	     )
	)
      )
    )
  )

(defun kami-indent-column ()
  (indent-line-to (diffParensPlusInit)))

(define-derived-mode kami-mode coq-mode "kami mode"
  "Major mode for editing Kami code"

  (setq font-lock-defaults '(kami-font-lock-keywords))
  (setq indent-line-function 'kami-indent-column)

  )

(provide 'kami-mode)
