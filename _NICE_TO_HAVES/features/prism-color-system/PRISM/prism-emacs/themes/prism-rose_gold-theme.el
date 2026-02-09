;;; prism-rose_gold-theme.el --- Prism Rose Gold theme -*- lexical-binding: t; -*-
;;; Commentary:
;; Prism Rose Gold color theme
;;; Code:

(deftheme prism-rose_gold
  "Prism Rose Gold - A dark theme.")

(let ((class '((class color) (min-colors 89)))
      (bg "#a5385f")
      (fg "#f7dcbc")
      (accent "#ffa6ab")
      (comment "#da627a")
      (hl "#8f3052"))

  (custom-theme-set-faces
   'prism-rose_gold
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

(provide-theme 'prism-rose_gold)
;;; prism-rose_gold-theme.el ends here
