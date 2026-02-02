;;; prism-acid_rain-theme.el --- Prism Acid Rain theme -*- lexical-binding: t; -*-
;;; Commentary:
;; Prism Acid Rain color theme
;;; Code:

(deftheme prism-acid_rain
  "Prism Acid Rain - A dark theme.")

(let ((class '((class color) (min-colors 89)))
      (bg "#0d1117")
      (fg "#bc8cff")
      (accent "#58a6ff")
      (comment "#7ee787")
      (hl "#161b22"))

  (custom-theme-set-faces
   'prism-acid_rain
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

(provide-theme 'prism-acid_rain)
;;; prism-acid_rain-theme.el ends here
