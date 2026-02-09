;;; prism-tessier-theme.el --- Prism Tessier theme -*- lexical-binding: t; -*-
;;; Commentary:
;; Prism Tessier color theme
;;; Code:

(deftheme prism-tessier
  "Prism Tessier - A light theme.")

(let ((class '((class color) (min-colors 89)))
      (bg "#ffffff")
      (fg "#1a2028")
      (accent "#0758c9")
      (comment "#6b7a8a")
      (hl "#f0f3f6"))

  (custom-theme-set-faces
   'prism-tessier
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

(provide-theme 'prism-tessier)
;;; prism-tessier-theme.el ends here
