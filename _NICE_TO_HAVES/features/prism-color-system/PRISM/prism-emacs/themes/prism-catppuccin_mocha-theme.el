;;; prism-catppuccin_mocha-theme.el --- Prism Catppuccin Mocha theme -*- lexical-binding: t; -*-
;;; Commentary:
;; Prism Catppuccin Mocha color theme
;;; Code:

(deftheme prism-catppuccin_mocha
  "Prism Catppuccin Mocha - A dark theme.")

(let ((class '((class color) (min-colors 89)))
      (bg "#1e1e2e")
      (fg "#fab387")
      (accent "#f38ba8")
      (comment "#cba6f7")
      (hl "#28283d"))

  (custom-theme-set-faces
   'prism-catppuccin_mocha
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

(provide-theme 'prism-catppuccin_mocha)
;;; prism-catppuccin_mocha-theme.el ends here
