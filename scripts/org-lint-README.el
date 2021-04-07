;;; org-lint-README ---- This is a simple Emacs script to lint the file README.org

;; Copyright (c) 2019 Nomadic Labs. <contact@nomadic-labs.com>
;; Author: Raphaël Cauderlier
;; Version: 0.1
;; License: MIT
;;; Commentary:
; This is inteded to be used in continuous integration using a command like
; $ emacs --batch -l scripts/org-lint-README.el --kill

;;; Code:

(require 'cl-lib)                           ; This defines the cl-assert macro

; Configuration of Emacs package manager
(require 'package)
(add-to-list 'package-archives '("org" . "https://orgmode.org/elpa/") t)
(package-initialize)
(package-refresh-contents)

; Ensure Org-mode is recent enough to provide the org-lint command
(package-install-file "scripts/org-lint-dummy.el")

; Gives access to org-lint--generate-reports
(require 'org-lint)

; Display versions of Emacs and Org-mode
(princ (format "Emacs version: %s\n" (emacs-version)))
(princ (format "Org version: %s\n" (org-version)))

;; Lint the README file
(find-file "README.org")                ; This opens the file in Org-mode
;; Call the linter and fail if it complains
(cl-assert (not (org-lint--generate-reports (current-buffer) org-lint--checkers))
           nil
           ;; Format error message
           (string-join
            (mapcar
             (lambda (el) (format "%s: %s" (aref (cadr el) 0) (aref (cadr el) 2)))
             (org-lint--generate-reports (current-buffer) org-lint--checkers) "\n")))

(provide 'org-lint-README)
;;; org-lint-README ends here
