// get the ninja-keys element
const ninja = document.querySelector('ninja-keys');

// add the home and posts menu items
ninja.data = [{
    id: "nav-about",
    title: "about",
    section: "Navigation",
    handler: () => {
      window.location.href = "/";
    },
  },{id: "nav-blog",
          title: "Blog",
          description: "",
          section: "Navigation",
          handler: () => {
            window.location.href = "/blog/";
          },
        },{id: "nav-bookshelf",
          title: "Bookshelf",
          description: "",
          section: "Navigation",
          handler: () => {
            window.location.href = "/books/";
          },
        },{id: "nav-lean",
          title: "Lean",
          description: "",
          section: "Navigation",
          handler: () => {
            window.location.href = "/lean/";
          },
        },{id: "nav-coursework",
          title: "Coursework",
          description: "",
          section: "Navigation",
          handler: () => {
            window.location.href = "/coursework/";
          },
        },{id: "nav-talks",
          title: "Talks",
          description: "",
          section: "Navigation",
          handler: () => {
            window.location.href = "/talks/";
          },
        },{id: "post-tutorial-a-verified-interpreter-with-side-effects",
        
          title: "Tutorial: A Verified Interpreter with Side Effects",
        
        description: "Part of the free monads series",
        section: "Posts",
        handler: () => {
          
            window.location.href = "/blog/2025/freer-monad-part4/";
          
        },
      },{id: "post-part-3-universal-morphisms-and-effect-handlers",
        
          title: "Part 3: Universal Morphisms and Effect Handlers",
        
        description: "Part of the free monads series",
        section: "Posts",
        handler: () => {
          
            window.location.href = "/blog/2025/freer-monad-part3/";
          
        },
      },{id: "post-part-2-initial-algebras-catamorphisms-and-interpreters",
        
          title: "Part 2: Initial Algebras, Catamorphisms, and Interpreters",
        
        description: "Part of the free monads series",
        section: "Posts",
        handler: () => {
          
            window.location.href = "/blog/2025/freer-monad-part2/";
          
        },
      },{id: "post-part-1-defining-the-free-monad-in-lean",
        
          title: "Part 1: Defining the Free Monad in Lean",
        
        description: "Introducing the categorical theory and implementation of free monads in Lean",
        section: "Posts",
        handler: () => {
          
            window.location.href = "/blog/2025/freer-monad-part1/";
          
        },
      },{id: "post-the-free-monad-a-four-part-series",
        
          title: "The Free Monad: A Four-Part Series",
        
        description: "A four-part series on free monads in Lean",
        section: "Posts",
        handler: () => {
          
            window.location.href = "/blog/2025/freer-monad/";
          
        },
      },{id: "post-verified-dynamic-programming-with-σ-types-in-lean",
        
          title: "Verified Dynamic Programming with Σ-types in Lean",
        
        description: "Solving a competitive programming problem and proving it correct with dependent types",
        section: "Posts",
        handler: () => {
          
            window.location.href = "/blog/2025/verified-dp/";
          
        },
      },{id: "books-analytic-idealism-in-a-nutshell",
          title: 'Analytic Idealism in a Nutshell',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/analytic-idealism-in-a-nutshell/";
            },},{id: "books-braiding-sweetgrass",
          title: 'Braiding Sweetgrass',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/braiding-sweetgrass/";
            },},{id: "books-categories-for-quantum-theory",
          title: 'Categories for Quantum Theory',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/categories-for-quantum-theory/";
            },},{id: "books-category-theory-in-context",
          title: 'Category Theory in Context',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/category-theory-in-context/";
            },},{id: "books-computational-complexity-a-modern-approach",
          title: 'Computational Complexity: A Modern Approach',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/computational-complexity-a-modern-approach/";
            },},{id: "books-ecofeminism-feminist-intersections-with-other-animals-and-the-earth",
          title: 'Ecofeminism: Feminist Intersections with Other Animals and the Earth',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/ecofeminism-feminist-intersections-with-other-animals-and-the-earth/";
            },},{id: "books-lectures-on-the-philosophy-of-mathematics",
          title: 'Lectures on the Philosophy of Mathematics',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/lectures-on-the-philosophy-of-mathematics/";
            },},{id: "books-the-logic-of-reliable-inquiry",
          title: 'The Logic of Reliable Inquiry',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/logic-of-reliable-inquiry/";
            },},{id: "books-logicomix-an-epic-search-for-truth",
          title: 'Logicomix: An Epic Search for Truth',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/logicomix-an-epic-search-for-truth/";
            },},{id: "books-modern-mathematical-logic",
          title: 'Modern Mathematical Logic',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/modern-mathematical-logic/";
            },},{id: "books-naming-and-necessity",
          title: 'Naming and Necessity',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/naming-and-necessity/";
            },},{id: "books-paths-to-god-living-the-bhagavad-gita",
          title: 'Paths to God: Living the Bhagavad Gita',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/paths-to-god-living-the-bhagavad-gita/";
            },},{id: "books-philosophy-of-mind-classical-and-contemporary-readings",
          title: 'Philosophy of Mind: Classical and Contemporary Readings',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/philosophy-of-mind-classical-and-contemporary-readings/";
            },},{id: "books-quintessence",
          title: 'Quintessence',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/quintessence/";
            },},{id: "books-rationalist-spirituality",
          title: 'Rationalist Spirituality',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/rationalist-spirit/";
            },},{id: "books-reality",
          title: 'Reality+',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/reality-plus/";
            },},{id: "books-tantra-illuminated",
          title: 'Tantra Illuminated',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/tantra-illuminated/";
            },},{id: "books-tao-te-ching",
          title: 'Tao Te Ching',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/tao-te-ching/";
            },},{id: "books-the-dao-of-functional-programming",
          title: 'The Dao of Functional Programming',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/the-dao-of-functional-programming/";
            },},{id: "books-the-joy-of-abstraction-an-exploration-of-math-category-theory-and-life",
          title: 'The Joy of Abstraction: An Exploration of Math, Category Theory, and Life',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/the-joy-of-abstraction-an-exploration-of-math-category-theory-and-life/";
            },},{id: "books-the-perennial-philosophy",
          title: 'The Perennial Philosophy',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/the-perennial-philosophy/";
            },},{id: "books-the-tao-is-silent",
          title: 'The Tao Is Silent',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/the-tao-is-silent/";
            },},{id: "books-the-zen-teachings-of-huang-po-on-the-transmission-of-mind",
          title: 'The Zen Teachings of Huang Po: On the Transmission of Mind',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/the-zen-teachings-of-huang-po-on-the-transmission-of-mind/";
            },},{id: "books-topoi-the-categorial-analysis-of-logic",
          title: 'Topoi: The Categorial Analysis of Logic',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/topoi-the-categorial-analysis-of-logic/";
            },},{id: "books-tractatus-logico-philosophicus",
          title: 'Tractatus Logico-Philosophicus',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/tractatus-logico-philosophicus/";
            },},{id: "books-type-theory-and-formal-proof",
          title: 'Type Theory and Formal Proof',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/type-theory-and-formal-proof/";
            },},{id: "books-types-and-programming-languages",
          title: 'Types and Programming Languages',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/types-and-programming-languages/";
            },},{id: "books-zhuangzi",
          title: 'Zhuangzi',
          description: "",
          section: "Books",handler: () => {
              window.location.href = "/books/zhuangzi/";
            },},{id: "news-a-simple-inline-announcement",
          title: 'A simple inline announcement.',
          description: "",
          section: "News",},{id: "news-a-long-announcement-with-details",
          title: 'A long announcement with details',
          description: "",
          section: "News",handler: () => {
              window.location.href = "/news/announcement_2/";
            },},{id: "news-a-simple-inline-announcement-with-markdown-emoji-sparkles-smile",
          title: 'A simple inline announcement with Markdown emoji! :sparkles: :smile:',
          description: "",
          section: "News",},{id: "projects-project-1",
          title: 'project 1',
          description: "with background image",
          section: "Projects",handler: () => {
              window.location.href = "/projects/1_project/";
            },},{id: "projects-project-2",
          title: 'project 2',
          description: "a project with a background image and giscus comments",
          section: "Projects",handler: () => {
              window.location.href = "/projects/2_project/";
            },},{id: "projects-project-3-with-very-long-name",
          title: 'project 3 with very long name',
          description: "a project that redirects to another website",
          section: "Projects",handler: () => {
              window.location.href = "/projects/3_project/";
            },},{id: "projects-project-4",
          title: 'project 4',
          description: "another without an image",
          section: "Projects",handler: () => {
              window.location.href = "/projects/4_project/";
            },},{id: "projects-project-5",
          title: 'project 5',
          description: "a project with a background image",
          section: "Projects",handler: () => {
              window.location.href = "/projects/5_project/";
            },},{id: "projects-project-6",
          title: 'project 6',
          description: "a project with no image",
          section: "Projects",handler: () => {
              window.location.href = "/projects/6_project/";
            },},{id: "projects-project-7",
          title: 'project 7',
          description: "with background image",
          section: "Projects",handler: () => {
              window.location.href = "/projects/7_project/";
            },},{id: "projects-project-8",
          title: 'project 8',
          description: "an other project with a background image and giscus comments",
          section: "Projects",handler: () => {
              window.location.href = "/projects/8_project/";
            },},{id: "projects-project-9",
          title: 'project 9',
          description: "another project with an image 🎉",
          section: "Projects",handler: () => {
              window.location.href = "/projects/9_project/";
            },},{
        id: 'social-email',
        title: 'email',
        section: 'Socials',
        handler: () => {
          window.open("mailto:%74%61%6E%6E%65%72%64%75%76%65@%67%6D%61%69%6C.%63%6F%6D", "_blank");
        },
      },{
        id: 'social-github',
        title: 'GitHub',
        section: 'Socials',
        handler: () => {
          window.open("https://github.com/tannerduve", "_blank");
        },
      },{
        id: 'social-linkedin',
        title: 'LinkedIn',
        section: 'Socials',
        handler: () => {
          window.open("https://www.linkedin.com/in/tannerduve", "_blank");
        },
      },{
      id: 'light-theme',
      title: 'Change theme to light',
      description: 'Change the theme of the site to Light',
      section: 'Theme',
      handler: () => {
        setThemeSetting("light");
      },
    },
    {
      id: 'dark-theme',
      title: 'Change theme to dark',
      description: 'Change the theme of the site to Dark',
      section: 'Theme',
      handler: () => {
        setThemeSetting("dark");
      },
    },
    {
      id: 'system-theme',
      title: 'Use system default theme',
      description: 'Change the theme of the site to System Default',
      section: 'Theme',
      handler: () => {
        setThemeSetting("system");
      },
    },];
