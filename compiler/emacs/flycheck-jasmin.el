;;; flycheck-jasmin.el --- Flycheck: Jasmin support    -*- lexical-binding: t; -*-

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

;; This Flycheck extension provides a syntax checker for the Jasmin language to
;; check Jasmin buffers for errors.
;;
;; # Setup
;;
;; Add the following to your init file:
;;
;;    ;; Enable Flycheck checker
;;    (flycheck-jasmin-setup))
;;
;; # Usage
;;
;; Just use Flycheck as usual in Jasmin Mode buffers. Flycheck will
;; automatically use the `jasmin` syntax checker if Jasmin Mode is enabled.

;;; Code:

(require 'flycheck)

(flycheck-define-checker jasmin
  "Flycheck Jasmin files using the standard compiler."
  :command ("jasmin" source)
  :error-patterns
  ((error line-start
          (one-or-more (not (any ":"))) ":" line ":" column
          (message)
          line-end))
  :modes jasmin-mode
  :predicate (lambda () t))


;;;###autoload
(defun flycheck-jasmin-setup ()
  "Setup Flycheck Jasmin.

Add `jasmin' to `flycheck-checkers'."
  (interactive)
  (add-to-list 'flycheck-checkers 'jasmin))

(provide 'flycheck-jasmin)

;;; flycheck-jasmin.el ends here
