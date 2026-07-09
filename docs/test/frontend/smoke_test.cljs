(ns frontend.smoke-test
  "Renders every tutorial page under happy-dom — catches broken hiccup,
  bad requires, missing snippet sources and missing captured results."
  (:require [cljs.test :refer-macros [deftest is testing]]
            [frontend.test-setup :refer [fresh-root]]
            [solidclj.api :as s]
            [solidclj.docs :as docs]
            [frontend.pages :as pages]))

(deftest every-page-renders
  (doseq [{:keys [pages]} pages/sections
          page            pages]
    (testing (name (:id page))
      (let [root    (fresh-root)
            dispose (s/render [docs/page-view page] root)]
        (try
          (is (pos? (.. root -innerHTML -length))
              (str (:id page) " should render non-empty HTML"))
          (is (.includes (.-textContent root) (:title page))
              (str (:id page) " should include its title"))
          (is (not (.includes (.-textContent root) "⚠"))
              (str (:id page) " should not show a missing-result warning"))
          (finally (dispose)))))))

(deftest example-source-is-syntax-highlighted
  (let [page    (->> pages/sections (mapcat :pages)
                     (some #(when (= :terminals (:id %)) %)))
        root    (fresh-root)
        dispose (s/render [docs/page-view page] root)]
    (try
      (is (.includes (.-innerHTML root) "hljs-")
          "code block should contain highlight.js token spans")
      (finally (dispose)))))

(deftest app-shell-renders-sidebar-and-home
  (let [root    (fresh-root)
        dispose (s/render [docs/app {:title "authz" :subtitle "tutorial"
                                     :sections pages/sections}] root)]
    (try
      (let [html (.-innerHTML root)]
        (is (.includes html "authz") "brand in sidebar")
        (is (.includes html "What is authz?") "home page selected by default")
        (is (.includes html "Occasionally connected") "sections listed"))
      (finally (dispose)))))
