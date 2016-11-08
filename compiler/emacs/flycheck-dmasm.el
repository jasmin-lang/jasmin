;;; flycheck-dmasm.el --- Flycheck: DMASM support    -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Benedikt Schmidt <beschmi@gmail.com>

;; Author: Benedikt Schmidt <beschmi@gmail.com>
;; URL: --
;; Package-Version: --
;; Keywords: convenience, tools, languages
;; Version: --
;; Package-Requires: ((emacs "24.1") (flycheck "0.22")

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This Flycheck extension provides a syntax checker for the DMASM language to
;; check DMASM buffers for errors.
;;
;; # Setup
;;
;; Add the following to your init file:
;;
;;    ;; Enable Flycheck checker
;;    (flycheck-dmasm-setup))
;;
;; # Usage
;;
;; Just use Flycheck as usual in DMASM Mode buffers. Flycheck will
;; automatically use the `dmasm` syntax checker if DMASM Mode is enabled.

;;; Code:

(require 'flycheck)

(flycheck-define-checker dmasm
  "Flycheck DMASM files using the standard compiler."
  :command ("dmasm" source)
  :error-patterns
  ((error line-start
          (one-or-more (not (any ":"))) ":" line ":" column
          (message)
          line-end))
  :modes dmasm-mode
  :predicate (lambda () t))


;;;###autoload
(defun flycheck-dmasm-setup ()
  "Setup Flycheck DMASM.

Add `dmasm' to `flycheck-checkers'."
  (interactive)
  (add-to-list 'flycheck-checkers 'dmasm))

(provide 'flycheck-dmasm)

;;; flycheck-dmasm.el ends here
