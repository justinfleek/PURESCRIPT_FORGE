;;; prism-fleek_gold-theme.el --- Prism Fleek Gold theme -*- lexical-binding: t; -*-
;;; Commentary:
;; Prism Fleek Gold color theme
;;; Code:

(deftheme prism-fleek_gold
  "Prism Fleek Gold - A dark theme.")

(let ((class '((class color) (min-colors 89)))
      (bg "#161616")
      (fg "#fefefe")
      (accent "#cbba9f")
      (comment "#9a886c")
      (hl "#1e1e1e"))

  (custom-theme-set-faces
   'prism-fleek_gold
   `(default ((,class (:background ,bg :foreground ,fg))))
   `(cursor ((,class (:background ,accent))))
   `(region ((,class (:background ,hl))))
   `(highlight ((,class (:background ,hl))))
   `(hl-line ((,class (:background ,hl))))
   `(fringe ((,class (:background ,bg))))
   `(line-number ((,class (:foreground ,comment))))
   `(line-number-current-line ((,class (:foreground ,fg))))
   `(font-lock-comment-face ((,class (:foreground ,comment :slant italic))))
   `(font-lock-keyword-face ((,class (:foreground ,accent))))
   `(font-lock-string-face ((,class (:foreground ,accent))))
   `(font-lock-function-name-face ((,class (:foreground ,fg))))
   `(font-lock-variable-name-face ((,class (:foreground ,fg))))
   `(font-lock-type-face ((,class (:foreground ,accent))))
   `(font-lock-constant-face ((,class (:foreground ,accent))))
   `(mode-line ((,class (:background ,hl :foreground ,fg))))
   `(mode-line-inactive ((,class (:background ,bg :foreground ,comment))))))

;;;###autoload
(when load-file-name
  (add-to-list 'custom-theme-load-path
               (file-name-as-directory (file-name-directory load-file-name))))

(provide-theme 'prism-fleek_gold)
;;; prism-fleek_gold-theme.el ends here
