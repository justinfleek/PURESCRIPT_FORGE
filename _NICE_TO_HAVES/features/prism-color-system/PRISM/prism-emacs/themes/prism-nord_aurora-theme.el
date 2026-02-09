;;; prism-nord_aurora-theme.el --- Prism Nord Aurora theme -*- lexical-binding: t; -*-
;;; Commentary:
;; Prism Nord Aurora color theme
;;; Code:

(deftheme prism-nord_aurora
  "Prism Nord Aurora - A dark theme.")

(let ((class '((class color) (min-colors 89)))
      (bg "#2e3440")
      (fg "#bf616a")
      (accent "#81a1c1")
      (comment "#88c0d0")
      (hl "#3b4252"))

  (custom-theme-set-faces
   'prism-nord_aurora
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

(provide-theme 'prism-nord_aurora)
;;; prism-nord_aurora-theme.el ends here
