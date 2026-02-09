;;; prism-mint-theme.el --- Prism Mint theme -*- lexical-binding: t; -*-
;;; Commentary:
;; Prism Mint color theme
;;; Code:

(deftheme prism-mint
  "Prism Mint - A light theme.")

(let ((class '((class color) (min-colors 89)))
      (bg "#EDFDEE")
      (fg "#1B445F")
      (accent "#74D2A9")
      (comment "#A6F2B8")
      (hl "#e0f5e1"))

  (custom-theme-set-faces
   'prism-mint
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

(provide-theme 'prism-mint)
;;; prism-mint-theme.el ends here
