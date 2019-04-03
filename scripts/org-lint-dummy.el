;;; org-lint-dummy.el ---- A dummy package to ensure a recent-enough version of org is installed

;; Copyright (c) 2019 Nomadic Labs. <contact@nomadic-labs.com>
;; Author: Raphaël Cauderlier
;; Version: 0.1
;; License: MIT
;; Package-Requires: ((org "9.0"))
;; Filename: org-lint-dummy.el
;;; Commentary:
; This package can be used to enforce existence of the org-lint
; command that was introduced in Org-mode version 9.0

;;; Code:
(require 'org)

(provide 'org-lint-dummy)
;;; org-lint-dummy.el ends here
