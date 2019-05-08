;; Syntax hightlighting and indentation for Kami code.
;; Author : Murali Vijayaraghavan
;; Organization : SiFive

(setq kami-keywords
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

(setq kami-types-and-vals
  '(
    "Bool"
    "Bit"
    "STRUCT"
    "Array"
    "Default"
    "WO"
    )
  )

(setq kami-keywords-regex (regexp-opt kami-keywords 'words))
(setq kami-types-and-vals-regex (regexp-opt kami-types-and-vals 'words))

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
			))
		(- init (point))
		0
		)
	     )
	)
      )
    )
  )

(defun kami-indent-column ()
  (interactive)
  (indent-line-to (diffParensPlusInit)))

(defun kami-indent-region (start end)
  (interactive "r")
  (save-excursion
    (goto-char start)
    (while (< (point) end)
      (indent-line-to (diffParensPlusInit))
      (forward-line 1))))

(global-set-key (kbd "<C-tab>") 'kami-indent-region)

(font-lock-add-keywords nil
			`(
			  (,kami-keywords-regex . font-lock-keyword-face)
			  (,kami-types-and-vals-regex . font-lock-builtin-face)
			  )
			't)
