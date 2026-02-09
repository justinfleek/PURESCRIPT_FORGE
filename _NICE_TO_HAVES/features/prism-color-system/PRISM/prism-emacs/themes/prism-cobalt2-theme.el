;;; prism-cobalt2-theme.el --- Prism Cobalt2 theme -*- lexical-binding: t; -*-
;;; Commentary:
;; Prism Cobalt2 color theme
;;; Code:

(deftheme prism-cobalt2
  "Prism Cobalt2 - A dark theme.")

(let ((class '((class color) (min-colors 89)))
      (bg "#193549")
      (fg "#80ffbb")
      (accent "#ff9d00")
      (comment "#ffc600")
      (hl "#1f4462"))

  (custom-theme-set-faces
   'prism-cobalt2
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

(provide-theme 'prism-cobalt2)
;;; prism-cobalt2-theme.el ends here
