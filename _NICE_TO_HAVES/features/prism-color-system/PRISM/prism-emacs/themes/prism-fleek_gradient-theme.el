;;; prism-fleek_gradient-theme.el --- Prism Fleek Gradient theme -*- lexical-binding: t; -*-
;;; Commentary:
;; Prism Fleek Gradient color theme
;;; Code:

(deftheme prism-fleek_gradient
  "Prism Fleek Gradient - A dark theme.")

(let ((class '((class color) (min-colors 89)))
      (bg "#0b0b0b")
      (fg "#30a46c")
      (accent "#ffe629")
      (comment "#0090ff")
      (hl "#151515"))

  (custom-theme-set-faces
   'prism-fleek_gradient
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

(provide-theme 'prism-fleek_gradient)
;;; prism-fleek_gradient-theme.el ends here
