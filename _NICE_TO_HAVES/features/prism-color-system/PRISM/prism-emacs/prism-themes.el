;;; prism-themes.el --- 40 formally verified color themes -*- lexical-binding: t; -*-

;; Copyright (C) 2026 Fleek AI

;; Author: Fleek AI <themes@fleek.sh>
;; Maintainer: Fleek AI <themes@fleek.sh>
;; Version: 1.0.0
;; Package-Requires: ((emacs "27.1"))
;; Keywords: faces, themes
;; URL: https://github.com/fleek-ai/prism-emacs
;; SPDX-License-Identifier: MIT

;;; Commentary:

;; Prism is a collection of 40 formally verified color themes built with
;; OKLCH color science for perceptual uniformity and WCAG AA compliance.
;;
;; Collections:
;; - Flagship: fleek, fleek-light
;; - Luxury: nero-marquina, midnight-sapphire, obsidian-rose-gold,
;;           champagne-noir, emerald-velvet, diamond-dust
;; - Glass: aurora-glass, zen-garden, tide-pool, porcelain-moon, soft-charcoal
;; - Harmonious: ocean-depths, forest-canopy, lavender-dusk, slate-and-gold,
;;               ember-hearth, constellation-map
;; - Wild: neon-nexus, blood-moon, vaporwave-sunset, acid-rain, ultraviolet,
;;         holographic, cyber-noir, synthwave-84
;; - Classic: catppuccin-mocha, dracula-pro, gruvbox-material, moonlight-ii,
;;            nord-aurora, one-dark-pro, ayu-mirage, rose-pine, night-owl,
;;            cobalt2, palenight, vesper, tokyo-night-bento
;;
;; Usage:
;;   (require 'prism-themes)
;;   (load-theme 'prism-fleek t)
;;
;; Or with use-package:
;;   (use-package prism-themes
;;     :ensure t
;;     :config
;;     (load-theme 'prism-fleek t))

;;; Code:

(defgroup prism-themes nil
  "Prism color themes."
  :group 'faces
  :prefix "prism-")

;;;###autoload
(when (and (boundp 'custom-theme-load-path) load-file-name)
  (let ((dir (file-name-as-directory
              (file-name-directory load-file-name))))
    (add-to-list 'custom-theme-load-path dir)
    (add-to-list 'custom-theme-load-path (concat dir "themes"))))

(defconst prism-themes-list
  '(prism-fleek
    prism-fleek-light
    prism-nero-marquina
    prism-midnight-sapphire
    prism-obsidian-rose-gold
    prism-champagne-noir
    prism-emerald-velvet
    prism-diamond-dust
    prism-aurora-glass
    prism-zen-garden
    prism-tide-pool
    prism-porcelain-moon
    prism-soft-charcoal
    prism-ocean-depths
    prism-forest-canopy
    prism-lavender-dusk
    prism-slate-and-gold
    prism-ember-hearth
    prism-constellation-map
    prism-neon-nexus
    prism-blood-moon
    prism-vaporwave-sunset
    prism-acid-rain
    prism-ultraviolet
    prism-holographic
    prism-cyber-noir
    prism-synthwave-84
    prism-catppuccin-mocha
    prism-dracula-pro
    prism-gruvbox-material
    prism-moonlight-ii
    prism-nord-aurora
    prism-one-dark-pro
    prism-ayu-mirage
    prism-rose-pine
    prism-night-owl
    prism-cobalt2
    prism-palenight
    prism-vesper
    prism-tokyo-night-bento)
  "List of all Prism themes.")

;;;###autoload
(defun prism-themes-load (theme)
  "Load a Prism THEME by name."
  (interactive
   (list (intern (completing-read "Load Prism theme: "
                                  (mapcar #'symbol-name prism-themes-list)
                                  nil t))))
  (load-theme theme t))

(provide 'prism-themes)

;;; prism-themes.el ends here
