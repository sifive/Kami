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
    "STRUCT_TYPE"
    "STRUCT_CONST"
    "Array"
    "ARRAY"
    "ARRAY_CONST"
    "Default"
    "WO"
    )
  )

(setq kami-keywords-regex (regexp-opt kami-keywords 'words))
(setq kami-types-and-vals-regex (regexp-opt kami-types-and-vals 'words))

(defun diff-parens-times-space (space)
  "Calculates the number of open parentheses minus closed parentheses in previous line,
   multiplies by space"
  (save-excursion
    (beginning-of-line)
    (let ((end (point)))
      (previous-line)
      (beginning-of-line)
      (let ((start (point))
	    (currind (current-indentation)))
	(+ (* space (- (how-many "[[({]" start end)
		       (how-many "[])}]" start end)
		       ))
	   currind)
	)
      )
    )
  )

(defun indent-region-parens-times-space (space start end)
  (save-excursion
    (goto-char start)
    (while (< (point) end)
      (indent-line-to (diff-parens-times-space space))
      (forward-line 1))))

(defun indent-region-parens-times-2 (start end)
  (interactive "r")
  (let ((space 2))
    (if (use-region-p)
	(indent-region-parens-times-space space start end)
      (indent-line-to (diff-parens-times-space space))
    )))

(global-set-key (kbd "<C-tab>") 'indent-region-parens-times-2)

(font-lock-add-keywords nil
			`(
			  (,kami-keywords-regex . font-lock-keyword-face)
			  (,kami-types-and-vals-regex . font-lock-builtin-face)
			  )
			't)
