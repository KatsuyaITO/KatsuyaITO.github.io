const searchInput = document.querySelector('#search');
const sortSelect = document.querySelector('#sort');
const grid = document.querySelector('#note-grid');
const cards = [...document.querySelectorAll('.note-card')];
const tagButtons = [...document.querySelectorAll('.tag')];
const count = document.querySelector('#result-count');
const emptyState = document.querySelector('#empty-state');
const resetButton = document.querySelector('#reset-filter');
const fullTextIndex = new Map();

let activeTag = 'all';

function normalize(value) {
  return value.toLocaleLowerCase('ja').normalize('NFKC');
}

function updateCards() {
  const query = normalize(searchInput.value.trim());
  let visible = 0;

  cards.forEach((card) => {
    const haystack = normalize(`${card.dataset.title} ${card.dataset.summary} ${card.dataset.tags} ${fullTextIndex.get(card) || ''}`);
    const matchesQuery = !query || haystack.includes(query);
    const matchesTag = activeTag === 'all' || card.dataset.tags.split(' ').includes(activeTag);
    const show = matchesQuery && matchesTag;
    card.hidden = !show;
    if (show) visible += 1;
  });

  count.textContent = visible;
  emptyState.hidden = visible !== 0;
}

async function indexArticlePages() {
  const searchableCards = cards.filter((card) => card.dataset.searchPage);

  await Promise.all(searchableCards.map(async (card) => {
    try {
      const response = await fetch(card.dataset.searchPage);
      if (!response.ok) return;

      const html = await response.text();
      const documentFragment = new DOMParser().parseFromString(html, 'text/html');
      const article = documentFragment.querySelector('.article-content, article, main');
      if (article) fullTextIndex.set(card, article.textContent);
    } catch {
      // Metadata search remains available when a page cannot be fetched.
    }
  }));

  updateCards();
}

function sortCards() {
  const mode = sortSelect.value;
  const sorted = [...cards].sort((a, b) => {
    if (mode === 'title') return a.dataset.title.localeCompare(b.dataset.title, 'ja');
    const difference = new Date(b.dataset.date) - new Date(a.dataset.date);
    return mode === 'oldest' ? -difference : difference;
  });
  sorted.forEach((card) => grid.appendChild(card));
}

tagButtons.forEach((button) => {
  button.addEventListener('click', () => {
    activeTag = button.dataset.tag;
    tagButtons.forEach((item) => item.classList.toggle('is-active', item === button));
    updateCards();
  });
});

searchInput.addEventListener('input', updateCards);
sortSelect.addEventListener('change', sortCards);

resetButton.addEventListener('click', () => {
  activeTag = 'all';
  searchInput.value = '';
  tagButtons.forEach((item) => item.classList.toggle('is-active', item.dataset.tag === 'all'));
  updateCards();
  searchInput.focus();
});

document.addEventListener('keydown', (event) => {
  if ((event.metaKey || event.ctrlKey) && event.key.toLowerCase() === 'k') {
    event.preventDefault();
    searchInput.focus();
  }
});

indexArticlePages();
