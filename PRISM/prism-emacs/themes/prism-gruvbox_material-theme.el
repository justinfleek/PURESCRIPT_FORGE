;;; prism-gruvbox_material-theme.el --- Prism Gruvbox Material theme -*- lexical-binding: t; -*-
;;; Commentary:
;; Prism Gruvbox Material color theme
;;; Code:

(deftheme prism-gruvbox_material
  "Prism Gruvbox Material - A dark theme.")

(let ((class '((class color) (min-colors 89)))
      (bg "#282828")
      (fg "#d3869b")
      (accent "#b8bb26")
      (comment "#fabd2f")
      (hl "#3c3836"))

  (custom-theme-set-faces
   'prism-gruvbox_material
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

(provide-theme 'prism-gruvbox_material)
;;; prism-gruvbox_material-theme.el ends here
