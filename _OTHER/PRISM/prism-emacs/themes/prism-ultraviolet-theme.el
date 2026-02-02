;;; prism-ultraviolet-theme.el --- Prism Ultraviolet theme -*- lexical-binding: t; -*-
;;; Commentary:
;; Prism Ultraviolet color theme
;;; Code:

(deftheme prism-ultraviolet
  "Prism Ultraviolet - A dark theme.")

(let ((class '((class color) (min-colors 89)))
      (bg "#1a0a2e")
      (fg "#50fa7b")
      (accent "#ff79c6")
      (comment "#bd93f9")
      (hl "#25103f"))

  (custom-theme-set-faces
   'prism-ultraviolet
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

(provide-theme 'prism-ultraviolet)
;;; prism-ultraviolet-theme.el ends here
