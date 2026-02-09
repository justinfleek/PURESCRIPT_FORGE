;;; prism-neoform-theme.el --- Prism Neoform theme -*- lexical-binding: t; -*-
;;; Commentary:
;; Prism Neoform color theme
;;; Code:

(deftheme prism-neoform
  "Prism Neoform - A light theme.")

(let ((class '((class color) (min-colors 89)))
      (bg "#e8ecf2")
      (fg "#2d3848")
      (accent "#0969da")
      (comment "#8896a8")
      (hl "#e8ecf2"))

  (custom-theme-set-faces
   'prism-neoform
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

(provide-theme 'prism-neoform)
;;; prism-neoform-theme.el ends here
